# `scheme-mcfa` — *m*-CFA for Scheme, reproduced in Ascent

A reproduction (with variations) of

> Davis Ross Silverman, Yihao Sun, Kristopher Micinski, Thomas Gilray.
> **So You Want To Analyze Scheme Programs With Datalog?**
> Scheme and Functional Programming Workshop, 2021.
> ([paper](https://arxiv.org/abs/2107.12909))

The paper implements a control-flow analysis (*m*-CFA, derived via the
*Abstracting Abstract Machines* methodology) for a significant subset of Scheme
— including `let`, multi-argument `lambda`, `if`, `set!`, `call/cc`, and binary
primitives — in the [Soufflé](https://souffle-lang.github.io/) Datalog engine.
The full Soufflé program is given in the paper's Appendix A.

This crate:

1. **Ports Appendix A to [Ascent](https://github.com/s-arash/ascent)**
   (Datalog embedded in Rust), following the Soufflé program closely — every
   Soufflé rule maps to an Ascent rule, and the Soufflé algebraic data types
   become Rust `enum`s/`struct`s.
2. **Generates the paper's worst-case term family** (Section 5, Figs. 11–12)
   and provides a **basic benchmark**.
3. **Cross-validates against the original Soufflé program** on identical input.
4. Adds two **variations**: tunable polyvariance `m` (0/1/2-CFA), reproducing
   the paper's headline observation that too little context makes the analysis
   explode; and a version representing syntax as structured data (a recursive
   enum matched in the rules) rather than flat id-relations — something Ascent
   supports but Soufflé's ADT indexing makes impractical.

## Layout

| File | Contents |
|------|----------|
| `src/lib.rs` | The faithful port of Appendix A. The `ascent!` block's comments name the corresponding operational-semantics / Appendix-A rule. Uses a single-id context `Context{ctx0:id}` exactly as the appendix does (`m = 1`). |
| `src/ast.rs` | The Scheme subset AST, the worst-case term generator (`worst_case_term`), and a feature-exercising term (`feature_term`). |
| `src/edb.rs` | Lowering of the AST to input facts (`Facts`), and a Soufflé `.facts` writer. |
| `src/generic.rs` | **Variation:** the same analysis generalized to a length-`m` contour, with `m` a runtime parameter (`analyze_generic`). |
| `src/structured.rs` | **Variation:** syntax represented as a recursive `Expr` enum matched structurally in the rules, instead of flat id-relations (`analyze_structured`). |
| `src/parallel.rs` | The generic analysis via `ascent_run_par!` (`analyze_generic_par`), for thread-scaling measurements. |
| `src/aam.rs` | A **hand-written AAM worklist** reference implementation — no Datalog, just a global store and an event-driven worklist (`analyze_aam`). |
| `src/tuned.rs` | The faithful port with **delta-friendly rules** (guards after joins, 3-atom joins split via materialized reader-index relations) — ~21× faster on deep terms. |
| `src/main.rs` | CLI runner / benchmarks. |
| `souffle/mcfa.dl` | The original Soufflé program, transcribed verbatim from Appendix A (only change: Soufflé 2.4.1 spells the nullary constructor `$MT()`). |
| `souffle/mcfa_adt.dl` | **Experiment:** a Soufflé version that carries syntax as an `expr` ADT instead of flat relations, to test whether ADTs regress performance. |
| `souffle/mcfa_tuned.dl` | **Experiment:** the Soufflé program tuned with per-version `.plan` directives and an internally-flattened store (148× on church(80)). |
| `tests/cross_check.rs` | Runs Ascent and Soufflé on the same input and asserts the outputs agree. |
| `tests/generic_check.rs` | Checks generic `m=1` ≡ the faithful port, reproduces the polyvariance/padding phenomena, and checks parallel ≡ sequential. |
| `tests/aam_check.rs` | Checks the hand-written AAM computes bit-for-bit the same relations as the Datalog, at `m ∈ {0,1,2}`. |
| `tests/tuned_check.rs` | Checks the tuned program computes the identical analysis to the faithful port (sizes + `stored_val`/`flow_ee` content). |
| `tests/structured_check.rs` | Checks the structured variant against the flat one (identical on duplicate-free terms; conflating on repeated subterms). |

## Running

```bash
# One run of the faithful (m=1) analysis on a worst-case term:
#   N = calls to f, K = nested + applications, P = identity padding
cargo run --release -p scheme-mcfa -- run 10 3 0

# The basic benchmark (a few-second sweep of term sizes):
cargo run --release -p scheme-mcfa -- bench

# The polyvariance variation: run 0/1/2-CFA on the same term:
cargo run --release -p scheme-mcfa -- cfa 8 3 0

# The structured-syntax variation vs. the flat one (same term, given m):
cargo run --release -p scheme-mcfa -- structured 8 2 0 1

# The "realistic" Church-arithmetic benchmark (sum of Church numerals 0..=N):
cargo run --release -p scheme-mcfa -- church 60

# Parallel run (thread count from RAYON_NUM_THREADS):
RAYON_NUM_THREADS=4 cargo run --release -p scheme-mcfa -- church-par 80 1

# Emit equivalent Soufflé .facts for a term:
cargo run --release -p scheme-mcfa -- emit-souffle /tmp/facts 10 3 0
```

## Cross-validation against Soufflé

`tests/cross_check.rs` lowers several terms (the feature term and worst-case
variants), runs both engines, and asserts that **every output relation has the
same cardinality** and that the pure-id relations (`flow_ee`, `freevar`,
`peek_ctx`, `copy_ctx`, `state_e`, addresses included) are **content-identical**.

```bash
# Requires `souffle` on PATH (or set SOUFFLE=/path/to/souffle).
cargo test --release -p scheme-mcfa
```

The port matches the original exactly. For example, on the term `N=10 K=3 P=0`
both engines derive `state_a = 111182`, `stored_val = 100032`, `flow_ee = 25`,
etc. (Ascent, in-memory, ≈0.8 s; compiled single-thread Soufflé, writing all
output relations to disk, ≈2.0 s.)

## The worst-case term family

Following Van Horn's construction (adapted for *m*-CFA in Section 5.1):

```scheme
((lambda (f)
   (let ((b0 (f 0)) (b1 (f 1)) ... (b_{N-1} (f (N-1))))
     b0))
 (lambda (z)
   PAD^P[ ((lambda (x) (+ z (+ z ...)))   ; K nested +
           (lambda (ix) ix)) ]))
```

`f` is applied to `N` distinct constants. When the analysis cannot keep those
calls apart, `z` takes all `N` abstract values, which then combine through the
`K` nested `+`s to yield `O(N^K)` distinct abstract `PrimVal`s — the polynomial
blow-up the paper studies.

## The polyvariance / padding phenomena

The `cfa` sub-command (and `tests/generic_check.rs`) reproduce the paper's
central results on this family:

```text
$ mcfa cfa 8 3 0                 $ mcfa cfa 8 3 1   (one padding layer)
  m       derived      time        m       derived      time
  0         83437   527 ms          0         83471   505 ms
  1         83509   527 ms          1         83551   536 ms
  2           503    10 ms          2         83614   535 ms
```

* **Insufficient polyvariance explodes.** With no padding, `m ∈ {0,1}` conflate
  the calls to `f` and blow up, while `m = 2` is precise (orders of magnitude
  smaller / faster).
* **Padding defeats a given polyvariance.** One identity-padding layer pushes
  the conflation past `m = 2`, so the previously-precise `m = 2` analysis now
  explodes too — exactly the mechanism the paper uses to construct
  worst-case terms for a chosen level of context sensitivity.

(The precision threshold sits one level higher than in the paper's Fig. 11
because our inner term has an extra binding between `z` and the `+`-chain; the
qualitative behaviour is identical.)

## Variation: syntax as structured data

The appendix represents *values* and *continuations* as Soufflé ADTs but
flattens *syntax* into id-keyed relations (`lambda`, `call`, `if`, `let`, …)
that rules join on by expression id — almost certainly because Soufflé indexes
and joins on ADTs poorly, so driving control flow by matching on recursive
syntax would be impractical there.

Ascent has no such restriction: a relation column can be any
`Clone + Eq + Hash` value, and rule bodies can pattern-match it. `structured.rs`
therefore represents syntax the *same* way the paper represents values and
continuations — as a recursive `Expr` enum — and **deletes the flat syntax
relations entirely**. Instead of

```rust
state_e(e, ctx, ak), if_(e, eg, et, ef)        // flat: join the `if` relation
```

a rule matches the structure directly:

```rust
state_e(e, ctx, ak), if let Expr::If(eg, et, ef) = &**e
```

`for`-clauses replace the arg-list relations (`for (pos, earg) in
args.iter().enumerate()`), and `freevar` becomes an ordinary precomputed Rust
function over the tree. The result is markedly shorter and, arguably, closer to
how one would write the analysis by hand.

**What changes.** Comparing structured vs. flat at the same `m` (via
`mcfa structured N K P m`):

```text
term N=8 K=2 P=0, m=1        flat (ids)   structured
  state_e                            65           56
  state_a                          4730         4707
  stored_val                       4122         4122   (identical)
  flow_ee / flow_aa            20 / 576     20 / 576   (identical)
  total derived                   10769        10714
  time                            36 ms        50 ms
```

Because expressions are compared *structurally* (exactly like the value ADTs),
structurally-identical subterms — the repeated `z` references, the identity
lambda used as padding, repeated literals — are **identified**. So the
structured analysis derives slightly fewer *expression-level* facts (`state_e`,
`flow_ea`), while the *value-flow* it computes (`stored_val`, `flow_ee`,
`flow_aa`, `copy_ctx`) is unchanged. On a term with no duplicate subexpressions
(e.g. `feature_term`) the two agree exactly, relation-for-relation
(`tests/structured_check.rs`).

**Cost.** Structural `Eq`/`Hash` on `Rc<Expr>` traverses the subtree, so joins
and indexing are `O(term size)` per operation rather than `O(1)` on an interned
id — the structured version runs ~15–35% slower here. Interning subterms (or
hashing on a cached node id) would recover most of that while keeping the
structured representation.

**Occurrence sensitivity.** If you want structured syntax *and* the id-based
analysis' occurrence semantics (distinguishing two textually-identical
subterms), use a *labelled* AST: give each node a unique id and key its
`Eq`/`Hash` on that id while still storing children inline. Rules still match on
structure; nothing is conflated. That is the representation most hand-written
CFA implementations use, and it is straightforward in Ascent — but impractical
in Soufflé for the same ADT-indexing reason.

## A realistic benchmark: Church arithmetic

The worst-case family is adversarial by construction. `church_term(n)` is an
ordinary functional program instead: it Church-encodes the naturals, builds
`0..=n` with the Church successor, sums them with Church `plus`, and reads the
result out. It is intensely higher-order — every number *is* a function and
`succ`/`plus` are shared — which is exactly the setting CFA exists for.

It also surfaces a real phenomenon. With an **arithmetic** read-out
(`(lambda (y) (+ y 1))`), the analysis builds an unbounded tower of `PrimVal`s
and blows up at *every* `m` (church(2) OOMs) — a faithful demonstration of why
`k`-CFA is intractable on natural higher-order arithmetic (Shivers; Van Horn &
Mairson). With an **identity** read-out the value domain stays finite, and the
benchmark scales smoothly with `n` (the workload is then the closure flow):

```text
church(sum 0..=N), faithful m=1 (Ascent)
  N=20   4844 derived    32 ms
  N=40  17074 derived   276 ms
  N=60  36904 derived   1.15 s
  N=80  64334 derived   3.36 s
```

## A hand-written AAM (no Datalog) — and how it compares

`src/aam.rs` implements the *same* `m`-CFA as a traditional Abstracting Abstract
Machine directly in Rust: a global value store and continuation store
(`VAddr → P(Value)`, `KAddr → P(Kont)`) and an event-driven, semi-naive
**worklist**. It reuses the *exact same* value/kont/context types as the
`generic` Datalog analysis and runs over the same input, so
`tests/aam_check.rs` can assert it computes bit-for-bit the same relations
(all sizes and `flow_ee` content, at `m ∈ {0,1,2}`).

Comparing all engines at `m = 1` (single thread; Soufflé is the compiled
`.printsize` binary; "tuned" versions apply the delta-friendly rewrites
described below — same fixpoint, verified; "generic" is the `ascent_run!`
version with a length-`m` vector context):

| term | Soufflé | **Soufflé tuned** | ascent! | **ascent tuned** | ascent generic | **AAM (raw Rust)** |
|------|---------|-------------------|---------|------------------|----------------|--------------------|
| worst-case `N=12 K=3 P=0` | 1.93 s | **0.88 s** | 1.92 s | 1.78 s | 4.0 s | 2.82 s |
| church(60) | 9.08 s | **0.109 s** | 1.17 s | **0.091 s** | 1.87 s | **0.045 s** |
| church(80) | 27.0 s | **0.182 s** | 3.21 s | **0.155 s** | 5.33 s | **0.082 s** |

Two very different regimes:

* On the **value-domain-dominated** worst-case term (the cost is the `PrimVal`
  blow-up), all engines are within ~3× — the work is irreducible
  set-manipulation of large nested values and the indexed joins are as good as
  the hand-written loop.
* On the **closure-flow-dominated** Church benchmark the naive ports are 1–2
  orders of magnitude slower than the AAM — but the *tuned* Ascent program
  closes most of that gap (3.21 s → 0.155 s, within ~2× of the AAM).

### Why: diagnosing the gap

It is *not* free-variable precomputation — `freevar` is a lower stratum that
the Datalog engines also saturate once (166 iterations, 9 ms on church(80);
the AAM's setup is likewise ~4 ms, visible under `MCFA_TIMING=1`).

The diagnosis comes from `MCFA_SUMMARY=1`, which prints Ascent's
`scc_times_summary()` (per-SCC iteration counts, and per-rule times when
`#![measure_rule_times]` is enabled):

* On church(80) the analysis SCC runs **21,273 iterations** deriving 64,334
  facts — **~3 new facts per iteration**. The deep curried structure makes the
  dataflow frontier tiny; the fixpoint crawls, one abstract machine step per
  round. (Worst-case `N=12`: 35 iterations, ~16,700 facts each — wide frontier,
  join work dominates, everything is fine.)
* Per-rule times show ~2.99 s of the 3.17 s concentrated in **four rule
  variants**, all with the same shape: the semi-naive variant whose delta is on
  a *later* body atom scans a big `total` index every round:
  - `state_a(v, ak), if gif_true(v), stored_kont(ak, ?If{..})` — the guard
    *between* the atoms defeats Ascent's runtime-reorderable simple join, so the
    delta=`stored_kont` variant iterates **all of `state_a`** (`indices_none`)
    each round. Same for the `?Closure` pattern in A-C/cc's first atom.
  - `state_e ⋈ call ⋈ peek_ctx` and `state_e ⋈ var ⋈ stored_val` — 3-atom
    rules: the variant with the delta on the third atom re-enumerates the whole
    2-atom prefix join each round.

  21,273 rounds × O(all states) ≈ quadratic. The AAM never rescans: it keeps
  *reverse* dependency indices (address → waiting variable-reads, kont-address →
  applied values, context → copy-edges), so each new fact touches exactly its
  readers.

### The fix is expressible in the rules (`src/tuned.rs`)

`McfaTuned` is the same analysis with three mechanical rewrites:

1. **guards/patterns moved after the joins** (`state_a(v, ak),
   stored_kont(ak, ?If{..}), if gif_true(v)`) — the two-atom join is then a
   simple join that Ascent evaluates from whichever side is smaller (the delta);
2. **3-atom joins split into binary joins** via intermediate relations
   (`app_state`, `let_state`, `callcc_state`, `var_read`, `copy_edge`) — these
   intermediates *are* the AAM's reader indices, materialized as relations;
3. **`stored_val`'s address flattened** to columns (`x, ctx, v`) so the store
   joins by key from either side.

`tests/tuned_check.rs` verifies it computes the identical analysis. The effect
on church(80): still ~25k iterations, but **5.5 µs/round instead of 154
µs/round** — 3.21 s → 0.155 s (~21×), with no regression on the worst-case
term. The residual ~2× vs the AAM is the irreducible rounds-based dispatch:
~25k rounds × ~55 rule variants, versus the worklist's 64k events each
processed once.

### Tuning Soufflé the same way: `.plan` + a flattened store

For a fair comparison, `souffle/mcfa_tuned.dl` applies the equivalent tuning to
the original Soufflé program. Soufflé's `.plan` directive is actually the
sharper tool here: it schedules each semi-naive *version* of a rule separately
(version *k* = delta on the *k*-th recursive body atom), so a 3-atom rule can
be delta-first in **every** version — something static atom reordering cannot
achieve, and what the Ascent tuning needed intermediate relations for. Two
mechanical accommodations: `.plan` is rejected on non-recursive clauses and
Soufflé clones multi-head rules per head, so the (non-recursive) `flow_*` heads
are split into separate unplanned rules; and the A-IfT disjunction is expanded
so plans can attach.

`.plan` alone: church(80) 27.0 s → 6.3 s (4.3×). Profiling the rest
(`souffle -p` + `souffleprof -c "rul <id>"`, which reports per-*version* time)
found the residue concentrated in the store rules, and the generated RAM
(`--show=transformed-ram`) shows why:

```text
FOR t0 IN @delta_state_e
 FOR t1 IN var ON INDEX t1.0 = t0.0
  FOR t2 IN stored_val              ← full scan, no index
   ... UNPACK t2.0 ... IF (t1.1 = t4.0 AND t0.1 = t4.1)
```

**Soufflé cannot drive an index probe from a freshly-constructed record key**:
`stored_val($VAddress(x, ctx), v)` with `x, ctx` bound and `v` free compiles to
scan-all + unpack + filter (records/ADTs are interned ids, and only *fully
bound* record values participate in index lookups). This is the strongest
evidence yet for the earlier hypothesis about why the paper keeps syntax in
flat relations: an ADT/record key is fine to *carry* (O(1) interned) and fine
to match when bound, but as a *lookup key with free companion columns* it
degrades to a scan. Flattening the store into columns internally
(`stored_val_f(x, ctx, v)`, with `stored_val` reconstructed once for output —
exactly what the Ascent tuning did) fixes it:

| church(80), `-j1` | time |
|---|---|
| Soufflé (appendix rules) | 27.0 s |
| + `.plan` on every recursive rule | 6.3 s |
| + flattened store | **0.182 s** (148×) |

The takeaway: the AAM's advantage was never "Rust vs Datalog" — it is that a
worklist is *frontier-driven by construction*, while semi-naive evaluation is
only frontier-driven if every rule version can start its join from its delta
(and every probe along the way is indexable). Written with that discipline,
*both* Datalog engines land within ~2× of the hand-written machine on the deep
Church term — and tuned Soufflé is actually the fastest engine on the wide
worst-case term.

## Performance: Ascent vs Soufflé, and thread scaling

Measured on a 4-core sandbox. "Soufflé" is the compiled program with
`.printsize` (it computes the full fixpoint but serializes only relation
sizes, matching Ascent's in-memory run — with full `.output` Soufflé is several
times slower still). "Ascent seq" is the faithful `m=1` port. Both compute the
identical fixpoint (verified by `cross_check`).

**Single thread:**

| term | Soufflé (`-j1`) | Ascent (seq) |
|------|-----------------|--------------|
| worst `N=10 K=3 P=0` | 0.71 s | 0.60 s |
| worst `N=12 K=3 P=0` | 2.10 s | 1.59 s |
| church(80) | 28.3 s | 3.4 s |

Ascent is competitive on the synthetic term and markedly faster (~8×) on the
Church benchmark.

**Thread scaling (1 / 2 / 4 threads):**

| | 1 | 2 | 4 |
|--|--|--|--|
| Soufflé, worst `N=12` (`-jN`) | 2.10 s | 2.10 s | 2.09 s |
| Soufflé, church(80) (`-jN`) | 28.3 s | 28.3 s | 28.1 s |
| Ascent `par`, worst `N=12` (`RAYON_NUM_THREADS`) | ~4.2 s | ~3.8 s | ~3.0 s |
| Ascent `par`, church(80) | 37.7 s | 36.3 s | 30.4 s |

* **Soufflé does not scale here** — the time is flat from 1 to 4 threads (the
  paper reports outright *anti*-scaling on larger runs). The paper's own
  explanation: their analysis "uses a large number of rules, and Soufflé does
  not parallelize across rules" — it parallelizes tuple work *within* one rule,
  so a program that is many small rules over modest relations has little to
  exploit and pays thread overhead.
* **Ascent's parallel backend scales positively but sublinearly** (~1.2–1.5× at
  4 cores). Note the parallel runtime (`ascent_run_par!`, concurrent hash maps)
  has a large constant overhead, and this measurement also uses the heavier
  length-`m` vector context, so parallel Ascent is *slower in absolute terms*
  than sequential Ascent for these workloads — the sequential port is the one
  to beat. (`parallel_matches_sequential` checks the two agree.)

## Does representing syntax as ADTs regress Soufflé?

`souffle/mcfa_adt.dl` carries syntax as an `expr` ADT (built inside Soufflé from
the *same* flat facts, so only the analysis representation differs). Comparing
compiled, single-thread, on the same single-binding term:

```text
term (single-binding worst-case)   flat (id relations)   ADT (structured)
  N=10 K=3                                 2.05 s               1.87 s  (0.91×)
  N=12 K=3                                 6.09 s               5.62 s  (0.92×)
```

Perhaps surprisingly, the ADT version is **not** slower — marginally faster,
because Soufflé **hash-conses** records/ADTs, so an `expr` used as an analysis
key is an O(1) interned integer internally, just like an id (and structural
sharing conflates duplicate subterms, so there are slightly fewer facts — the
same effect as the Rust `structured` variant).

So for *this* analysis the cost hypothesis doesn't hold; the real friction with
ADT-syntax in Soufflé is **expressiveness/ergonomics**, not key cost:

* Soufflé rejects wildcards inside an ADT branch match — `e = $EIf(g, _, _)`
  fails with *"Ungrounded ADT branch"*; every field must be named
  (`e = $EIf(g, _t, _f)`).
* Variable-arity syntax (multi-argument lambdas, multi-binding `let`,
  argument lists) has no natural fixed-arity ADT encoding, so `mcfa_adt.dl` is
  restricted to single-argument / single-binding terms (`worst_case_term_single`);
  the flat relations handle arbitrary arity directly. This is likely the
  practical reason the appendix keeps *syntax* flat while using ADTs for values
  and continuations.
* You cannot build a join index on a field *nested inside* an ADT without first
  destructuring it into a helper relation.

## Notes

* The faithful port uses the appendix's single-id context, i.e. `m = 1`. The
  `generic` module generalizes this to a bounded length-`m` contour; at `m = 1`
  it produces bit-for-bit the same flow graph as the faithful port (checked in
  `tests/generic_check.rs`).
* Soufflé prints a few "variable occurs once" warnings on `mcfa.dl`; these
  singleton variables are present in the appendix as published and are harmless.
