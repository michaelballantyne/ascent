# `scheme-mcfa-plusplus` — evaluating the `plusplus` Ascent fork on the m-CFA ports

The [`plusplus` branch](https://github.com/michaelballantyne/ascent/tree/plusplus)
is Yihao Sun's research fork of Ascent (one of the authors of the paper this
crate family reproduces — the fork adds to Ascent the Slog-inspired features
that paper motivated). This crate evaluates the fork's extra features against
the m-CFA implementations in the parent `scheme-mcfa` crate: which ones
actually improve them, which are orthogonal, and what broke along the way.

**Wiring.** The fork branched from ascent ~0.7 and rewrote the macro
internals, while this repo's workspace carries ascent 0.8+ — a merge is
infeasible. Instead this crate takes the fork as a pinned git dependency
(`rev 4f80fa1`); Cargo hosts both semver-incompatible `ascent` packages in
one graph (0.7 here, 0.8 via the `scheme-mcfa` path dependency). Inside this
crate, `ascent::ascent!` *is* the fork.

## Result 1 (the win): explicit `delta` markers replace the tuned port's intermediate relations — and beat it

The parent crate's diagnosis ("frontier-blindness", see its README) was that
on deep terms the fixpoint runs ~21k iterations deriving ~3 facts each, and
every semi-naive rule *version* whose delta sits on a later body atom rescans
the whole total-side prefix each round — quadratic. `tuned.rs` fixed this by
materializing reader-index relations (`app_state`, `var_read`, `copy_edge`,
…). Soufflé fixed it more sharply with `.plan`, which schedules each
semi-naive version separately (148× there).

The fork has the `.plan` idea as *syntax*: marking a body atom `delta`
compiles the rule to a **single** semi-naive version — delta on the rule's
first dynamic atom, total+delta on the rest. Writing one delta-first rule per
dynamic atom is then a complete manual enumeration of the semi-naive
versions, each scheduled delta-first:

```rust
// (a) delta on state_a                      // (b) delta on stored_kont
... <-- delta state_a(v, ak),                ... <-- delta stored_kont(ak, ?Kont::Let{..}),
        stored_kont(ak, ?Kont::Let{..});             state_a(v, ak);
```

`src/delta_flat.rs` (`McfaDelta`) applies this to the faithful flat port:
every two-dynamic-atom rule in the analysis SCC becomes an (a)/(b) pair;
nothing else changes — **no intermediate relations, no flattened store**. The
reversed versions probe existing indices directly (e.g. `delta
stored_val(?AddrV{x, ctx}, v)` destructures the address, then probes `var`
and `state_e` on the bound key) — they *are* the delta worklist's reverse
dependency indices, expressed as rule order. `tests/delta_flat_check.rs`
verifies content-identical relations to `scheme_mcfa::analyze`.

`delta_bench` (this sandbox, single thread, m = 1):

| term | faithful | tuned | **delta (this crate)** | AAM delta worklist |
|---|---:|---:|---:|---:|
| worst `N=12 K=3 P=0` | 2.03 s | 1.69 s | 2.02 s | 2.39 s |
| church(60) | 1.01 s | 84 ms | **70 ms** | 29 ms |
| church(80) | 3.19 s | 153 ms | **131 ms** | 56 ms |

On the deep Church terms the delta-first rewrite alone is ~15% *faster* than
the tuned port (`MCFA_SUMMARY=1`: the full 21,273 iterations run in ~118 ms,
~5.6 µs/round — no rescans remain) while staying a line-for-line copy of the
faithful rules. On the join-heavy worst-case term the doubled rule count
costs ~1.2× vs tuned (on par with the faithful port). This is the one fork
feature we'd adopt outright — an explicit per-version schedule is strictly
less machinery than materialized intermediates, and something upstream
Ascent could add as a small, orthogonal extension.

## Result 2 (the honest negative): the Slog-style features solve problems embedded Ascent doesn't have

`src/slog_style.rs` (+ `slog_style/{baseline,mcfa_frag}.rs`) assesses
`relation ID` / `>?id.` / `.id`, `!` head dependencies, and
`function`/defunctionalization, by rebuilding a reduced m-CFA (m = 0) with
expressions, values, and continuations all as ID-relation rows referenced by
`Tag` — cross-checked against `analyze_structured` — plus the fork README's
own `path_length` example. Full discussion in `slog_style.rs`'s doc comment;
verdicts:

* **`relation ID`** mints identity for facts discovered *during* the
  fixpoint with no prior handle. m-CFA has no such facts: syntax identity is
  source position, and addresses are structural compositions of known
  values. Applied to syntax anyway, it silently **hash-conses by content**
  (probe included) — recovering the coarser `to_expr` identity the parent
  crate shows can lose precision — and `Tag` references reintroduce
  join-back-to-read-fields, the same friction the parent crate's Soufflé ADT
  experiment documents. Vanilla Ascent's structured Rust columns already do
  everything this feature offers here, minus ~15 lines of manual labeling.
* **`!` (only-if-new heads)** is a real primitive, but monotone m-CFA never
  asks the question; its only role here is as plumbing inside the other
  features' desugaring.
* **`function`** is magic-sets-as-a-keyword, and it works — after routing
  around a genuine fork bug (below). Its demand-drivenness pruned real work
  exactly once in the fragment (an unreached `if` branch); everywhere else
  the m-CFA fixpoint already *is* a tight reachability bound, leaving
  nothing for the rewrite to prune. Slog's motivating `path_length` case
  differs in kind: there the function is the whole computation.

## Result 3 (capability, with a sharp edge): incremental / streaming analysis

`src/incremental.rs` feeds the EDB to `McfaDelta` in chunks, continuing the
fixpoint per chunk. The mechanism that works (verified against the fork's
codegen): assign each plain EDB `Vec` field *only the new chunk* and call
plain `run()` — `update_indices_priv()` is additive, and is also the only
reader of plain fields, so the documented-looking `run_with_init_flag(false)`
route silently ignores plain-field injection (that flag exists for the
phantom-relation route, which needs the fork's byods crate).
`tests/incremental_check.rs` verifies chunked arrival converges to the
batch-identical fixpoint.

Verdict: **streaming works; "small edit → instant re-analysis" does not.**
Total work across chunks stays close to one batch run (church(40): 39 ms
incremental vs 40 ms batch). But the fork's `scc_pre` unconditionally replays
the entire accumulated `total` into `delta` on *every* `run()`, so a
continuation costs proportional to the analysis accumulated so far, not to
the injection: a 2.5%-of-facts final chunk costs 34 ms against the 40 ms
batch. Neither base Ascent nor Soufflé offers even this much, but true
incremental would need the replay to go.

## Fork bugs and doc gotchas found (all with minimal repros in the tests)

1. **Reference-typed `extern arguement`s miscompile**: codegen forwards
   extern args between SCC functions via `.clone()`; for `&Vec<T>` autoderef
   picks `Vec::clone`, changing the argument's type mid-pipeline. The fork's
   own tests dodge it only because `mpsc::Receiver` isn't `Clone`. Workaround:
   owned arguments. (`tests/delta.rs`.)
2. **`function` with a non-`Copy` return type double-moves** the return
   variable in generated code (`E0382`; two-line repro:
   `function f(usize) -> String;`), and the return binding accepts only an
   ident, so no source-level fix exists. Workaround: return a `Copy` ref
   (`Tag`) and resolve through a side table. (`tests/slog_style_check.rs`,
   `#[ignore]`d repro.)
3. **README syntax drift**: filter-by-bound-id is spelled `rel(args).*pid`
   (deref) in the fork's working tests; the README's `rel(args).pid` parses
   but silently *shadows* instead of filtering.

## Layout

| File | Contents |
|------|----------|
| `src/delta_flat.rs` | `McfaDelta`: faithful flat port with manually enumerated delta-first rule versions. |
| `src/slog_style.rs` + `src/slog_style/` | Slog-features expressiveness study; verdict doc + baseline + m-CFA fragment. |
| `src/incremental.rs` | Chunked-EDB incremental analysis + timing demo (`incremental_timing_demo -- --nocapture`). |
| `src/bin/delta_bench.rs` | The benchmark table above (`cargo run --release -p scheme-mcfa-plusplus --bin delta_bench`). |
| `tests/delta.rs`, `tests/id_relation.rs` | Feature smoke tests (delta marker vs normal semi-naive; `relation ID`). |
| `tests/delta_flat_check.rs`, `tests/slog_style_check.rs`, `tests/incremental_check.rs` | Cross-checks against the parent crate's analyses. |
