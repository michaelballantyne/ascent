# `egglog/` — *m*-CFA for Scheme, ported to egglog

A port of this crate's control-flow analysis to
[egglog](https://github.com/egraphs-good/egglog) (Datalog + equality
saturation over a hash-consed term store; measured here with the egglog
**2.0.0** release binary, `cargo install egglog`).

It joins the flat Soufflé/Ascent ports and the structured Slog port as
another representation of the *same* analysis (identical fixpoint, verified):

| representation | syntax carried as | values/konts carried as | file |
|---|---|---|---|
| flat id-relations (paper's Appendix A) | input relations keyed by node id | Soufflé ADTs / Rust enums | `../souffle/mcfa.dl`, `../src/lib.rs` |
| **flat id-relations (egglog)** | **the same input relations** | **egglog datatypes (hash-consed e-nodes)** | **`mcfa.egg`** |

## Files

| file | contents |
|---|---|
| `mcfa.egg` | the whole analysis: the `datatype*` declarations for contexts/addresses/values/continuations, the EDB relation declarations, and every machine rule, one egglog rule per Soufflé rule. |
| `run.egg` | the driver tail: `(run-schedule (saturate (run)))` + `(print-size)`. |

## Running

```bash
# emit a term's input facts as one .egg file (includes precomputed freevar):
cargo run --release -p scheme-mcfa -- emit-egglog /tmp/facts.egg worst 12 3 0
cargo run --release -p scheme-mcfa -- emit-egglog /tmp/facts.egg church 80

# run the analysis and print every relation's size:
egglog mcfa.egg /tmp/facts.egg run.egg

# expected sizes, for cross-checking:
cargo run --release -p scheme-mcfa -- expected worst 12 3 0
```

## The port

egglog turns out to be the *most direct* host for the appendix so far — the
program is shorter than the Soufflé original, with none of the accommodations
the other engines needed:

* **Nested constructor patterns are allowed anywhere in a rule body.** The
  A-rules match the continuation store through its constructor directly —
  including *two* levels of nesting in A-Call:

  ```lisp
  (rule ((state_a v ak) (stored_kont ak (KFn (VClosure elam ctxclo) pos ectx nak))
         (lambda elam params ebody) (lambda_arg_list params pos x))
        ((state_e ebody ectx nak)
         (stored_val (VAddress x ectx) v)
         (copy_ctx ctxclo ectx elam)
         (flow_ae v ebody)))
  ```

  Soufflé parses the same pattern but compiles a record key with free
  companion columns to scan-unpack-filter (the 148× `mcfa_tuned.dl` fix);
  Ascent needed `if let` guards moved after the joins; Flix rejects
  constructor patterns in bodies outright. egglog's datatypes are function
  tables in the database, so the planner decomposes the pattern into
  *indexed joins on interned ids* — the store is queried through a
  constructed key at full speed, with nothing to rewrite. (At two levels of
  nesting this stops being free — see the profile below — but it is
  *correct and indexed* out of the box.)
* **Values are hash-consed by the engine.** A `Val` term is an e-node: the
  giant nested `PrimVal` values the worst-case term family produces are
  interned once and compared as integer ids ever after — the same trick
  `mcfa_adt.dl` showed helps Soufflé, taken further. This is where egglog's
  worst-case-term win (below) comes from: Ascent hashes those nested Rust
  enums structurally on every probe.
* **Multi-head Soufflé rules are one egglog rule with several head actions**
  (no body duplication), and Soufflé's `;`-disjunctions become one rule per
  disjunct (A-IfT's four value shapes, `peek_ctx`'s four forms).
* **No negation exists in egglog**, so the (stratified) `freevar` relation is
  precomputed and shipped as input facts — `mcfa emit-egglog` runs a
  freevar-only Ascent program (`src/freevar.rs`, the ten rules verbatim) and
  emits the result. This mirrors what `structured.rs` does in Rust. It is the
  one piece of the paper's program that egglog cannot express; everything
  else is derived in-engine. (`freevar` costs the other engines a few
  milliseconds, so this does not distort the comparison.)
* The equality-saturation half of egglog is deliberately unused: nothing is
  ever `union`ed, so the e-graph degenerates to exactly the hash-consed term
  store the analysis wants. The "abstraction via merge" direction (e.g.
  unioning contexts to coarsen polyvariance) is an intriguing follow-up this
  port does not explore.

**Correctness.** All ten output relations (`state_e`, `state_a`,
`stored_val`, `stored_kont`, `flow_ee/ea/ae/aa`, `peek_ctx`, `copy_ctx`)
match the Ascent fixpoint's cardinalities *exactly* — on the feature term,
`worst 4 2 0`, `church 10`, `worst 12 3 0` (585 k derived facts), and
`church 60` — via `mcfa expected`. The port worked on the first run, which
says something about how little impedance mismatch there is.

## Performance: two regimes, sharper than ever

Same machine, same terms as the crate README's engine table (in-process
engines exclude fact prep; egglog numbers are whole-process `time`, of which
parse/load is ~10 ms on `worst` and ~0.45 s on `church(80)` — measured with a
no-op schedule):

| engine (single thread) | worst `N=12 K=3` | church(60) | church(80) |
|---|---:|---:|---:|
| ascent (flat, faithful) | 1.57 s | 1.07 s | 3.22 s |
| ascent (flat, tuned) | 1.45 s | 0.089 s | 0.137 s |
| AAM (delta worklist) | 2.09 s | 0.026 s | 0.044 s |
| **egglog** | **0.63 s** | 3.5 s | 7.0 s |

* **On the join-heavy worst-case term egglog is the fastest engine in the
  repo** — ~2.3× faster than tuned Ascent, ~3.3× faster than the
  hand-written delta worklist, with the *untuned, straight-off-the-appendix*
  rule set (and the margin repeats at `N=8`: 0.10 s vs 0.25 s / 0.27 s).
  The fixpoint there is 36 wide rounds dominated by the `Prim2 × values`
  product over huge nested `PrimVal`s; egglog runs it as indexed joins over
  interned ids (`--save-report`: A-Prim2 140 ms + A-Let 109 ms of 281 ms
  total search/apply). Hash-consing the value domain is precisely the right
  representation for this term family.
* **On the deep Church terms egglog is frontier-blind at the *engine* level**
  — ~40–50× slower than tuned Ascent, ~2–3× slower even than *naive*
  Ascent. `church(60)` needs 12,374 iterations; the report splits the time
  as search+apply 520 ms / merge 55 ms / **rebuild 631 ms** — the post-round
  congruence/index maintenance alone outweighs every rule body combined,
  and neither is where a Datalog tuner can reach (see below). Per-round
  overhead × tens of thousands of tiny rounds is the whole story, the same
  diagnosis as the crate README's "frontier-blindness" — but here it is the
  runtime's fixed cost per round, not a rescanned join.
* **Parallelism follows the same split**: `-j4` shaves ~20% off the
  worst-case term (0.63 s → ~0.52 s) but makes the Church terms ~2.3×
  *slower* (church(60) 3.6 s → 8.3 s, church(80) 7.0 s → 15.3 s) — with ~3
  new facts per round there is nothing to parallelize, and the per-round
  fork/join overhead compounds 12 k times.

## Why there is no `mcfa_tuned.egg`

The delta-friendly rewrites that bought 15× in Ascent and 148× in Soufflé
were tried here and **made egglog slower**. This negative result is worth
recording precisely:

1. **Splitting 3-atom joins through intermediate relations** (`app_state`,
   `let_state`, `callcc_state`, `var_read`, `copy_edge`, plus a
   `fn_call_state` to de-nest A-Call's 2-level pattern — the exact
   `src/tuned.rs` treatment): verified correct, but church(60) went 3.5 s →
   4.8 s and worst 0.63 s → 0.80 s. egglog's `(run)` rounds are
   *synchronized*: a fact produced in round *N* is visible in round *N*+1,
   so every intermediate relation adds one round of latency to every event
   flowing through it — iterations rose 12,374 → 18,624 — and the rebuild
   pass, whose cost scales with table count/size, nearly doubled (631 ms →
   1,310 ms). The de-nesting itself *did* work (search+apply fell 520 ms →
   338 ms; A-Call-closure alone had been 263 ms, 51% of all rule time, at
   ~68 µs/match because the planner compiles `KFn(VClosure(..)..)` into a
   join across two constructor tables) — it just cost more in rounds and
   rebuild than it saved. In Ascent the same intermediates are nearly free
   because its per-round cost is ~µs and it has no rebuild phase at all.
2. **Flattening the store key** (`stored_val (String Ctxt Val)` instead of
   `(AddrV Val)`, and inlining the `AddrV` payloads of `KLet`/`KSet`):
   ~2% on church(60), ~6% on church(80), but a reproducible ~5% *regression*
   on the worst-case term — `AddrV` is itself hash-consed, so the original
   single-id key was already optimal for a 249 k-row store. Not worth
   trading the headline win for.
3. **No scheduling escape hatch (yet).** Upstream egglog has per-rule
   `:naive`/`:no-decomp` options and a `--no-decomp` flag that might have
   kept the A-Call de-nesting without the extra-relation tax, but the 2.0.0
   release binary rejects all three (`parse error: could not parse rule
   option`) — they are newer than the release. There is also no analogue of
   Soufflé's `.plan`: join planning is entirely automatic.

So the straightforward port *is* the tuned port: its rule shape is already
delta-driven everywhere Ascent needed hand-splitting (egglog's planner
handles the delta-on-third-atom variants fine — E-Call/E-Let cost almost
nothing in the profile), and the residual Church-term gap sits in per-round
rebuild machinery that rule-level rewrites can only add to. A fair summary:
**egglog gives you the tuned-Datalog join behaviour by default, but its
e-graph bookkeeping prices every round as if you might have unioned
something — which this analysis never does.**

## egglog quirks encountered

* `(print-size)` prints `name: count` lines (the docs' S-expression format
  is newer than the 2.0.0 release); `(print-size relname)` prints one bare
  integer.
* Timing must come from `--save-report <json>` (per-rule
  `search_and_apply`/`merge`/`rebuild` times and per-iteration lists) or
  `RUST_LOG=info`; `(run-schedule ...)` itself prints nothing.
* Facts are just top-level actions — `(call "e1" "e2" "a0")` — so an input
  file is declarations-free and can be concatenated with the program on the
  CLI: `egglog mcfa.egg facts.egg run.egg` runs all three in one program
  state.
* `(datatype* ...)` is required for the mutually recursive
  `Val`/`Kont`/`AddrK` group.
