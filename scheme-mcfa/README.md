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
4. Adds several **variations**: tunable polyvariance `m` (0/1/2-CFA),
   reproducing the paper's headline observation that too little context makes
   the analysis explode; a version representing syntax as structured data (a
   recursive enum matched in the rules) rather than flat id-relations, in two
   labelings — hash-consed (structural identity) and per-occurrence (Ascent
   expresses this directly; in Soufflé the obstacle turns out to be ADT
   *ergonomics*, not join cost — see the ADT experiment below); **two
   hand-written machines with no Datalog at all** (a textbook step machine and
   an event-driven delta worklist), checked content-identical to the Datalog
   fixpoint; and **delta-friendly "tuned" rule sets** for both the flat and
   structured ports, closing most of the gap the machines expose.

## Layout

| File | Contents |
|------|----------|
| `src/lib.rs` | The faithful port of Appendix A. The `ascent!` block's comments name the corresponding operational-semantics / Appendix-A rule. Uses a single-id context `Context{ctx0:id}` exactly as the appendix does (`m = 1`). |
| `src/ast.rs` | The Scheme subset AST, the worst-case term generator (`worst_case_term`), and a feature-exercising term (`feature_term`). |
| `src/edb.rs` | Lowering of the AST to input facts (`Facts`), and a Soufflé `.facts` writer. |
| `src/generic.rs` | **Variation:** the same analysis generalized to a length-`m` contour, with `m` a runtime parameter (`analyze_generic`). |
| `src/structured.rs` | **Variation:** syntax represented as a recursive `Expr` enum matched structurally in the rules, instead of flat id-relations (`analyze_structured`). Nodes are labelled: `to_expr` hash-conses (structural identity), `to_expr_labeled` keeps every occurrence distinct (id semantics). |
| `src/tuned.rs` | The faithful port with **delta-friendly rules** (guards after joins, 3-atom joins split via materialized reader-index relations) — ~15–20× faster on deep terms. |
| `src/structured_tuned.rs` | The same delta-friendly treatment applied to the **structured** port (`analyze_structured_tuned`); structured syntax needs fewer intermediates. |
| `src/aam.rs` | **No Datalog #1:** a textbook abstract machine — state → state `step`, dedup'd FIFO work-set, dependency-tracked re-firing — over the labelled syntax (`analyze_aam`). |
| `src/aam_delta.rs` | **No Datalog #2:** an event-driven worklist — each derived fact processed exactly once against reverse dependency indices; semi-naive evaluation by hand (`analyze_aam_delta`). |
| `src/parallel.rs` | The generic analysis via `ascent_run_par!` (`analyze_generic_par`), for thread-scaling measurements. |
| `src/main.rs` | CLI runner / benchmarks. |
| `souffle/mcfa.dl` | The original Soufflé program, transcribed verbatim from Appendix A (only change: Soufflé 2.4.1 spells the nullary constructor `$MT()`). |
| `souffle/mcfa_adt.dl` | **Experiment:** a Soufflé version that carries syntax as an `expr` ADT instead of flat relations, to test whether ADTs regress performance. |
| `tests/cross_check.rs` | Runs Ascent and Soufflé on the same input and asserts the outputs agree. |
| `tests/generic_check.rs` | Checks generic `m=1` ≡ the faithful port, reproduces the polyvariance/padding phenomena, and checks parallel ≡ sequential. |
| `tests/structured_check.rs` | Checks the structured variant against the flat one: the occurrence-labelled tree matches on every term; hash-consing conflates repeated subterms — merging states on some terms, losing precision on others. |
| `tests/aam_check.rs` | Checks both hand-written machines derive **content-identical** relations (states, stores, flow graph) to the Ascent program, on both labelings, at `m = 0/1/2`. |
| `tests/tuned_check.rs` | Checks the tuned programs compute the identical analysis to their untuned counterparts (flat: sizes + `stored_val`/`flow_ee` content; structured: all relation sizes, both labelings, `m = 0/1/2`). |

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

# The direct (no-Datalog) step machine vs. the Ascent program, relation by relation:
cargo run --release -p scheme-mcfa -- aam 10 3 0 1
cargo run --release -p scheme-mcfa -- aam-church 60 1

# All seven engines on one term (worst N K P | church N), at m=1:
cargo run --release -p scheme-mcfa -- engines worst 12 3 0
cargo run --release -p scheme-mcfa -- engines church 80
MCFA_SUMMARY=1 cargo run --release -p scheme-mcfa -- engines church 80  # + per-SCC summaries

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
that rules join on by expression id. The reason is not join cost — Soufflé
hash-conses ADTs, and the ADT experiment below shows ADT-carried syntax is not
slower there — but expressiveness: Soufflé rejects wildcards inside an ADT
branch match, and variable-arity forms have no natural fixed-arity ADT
encoding.

Ascent has neither restriction: a relation column can be any
`Clone + Eq + Hash` value, and rule bodies can pattern-match it. `structured.rs`
therefore represents syntax the *same* way the paper represents values and
continuations — as a recursive `Expr` — and **deletes the flat syntax
relations entirely**. Instead of

```rust
state_e(e, ctx, ak), if_(e, eg, et, ef)        // flat: join the `if` relation
```

a rule matches the structure directly:

```rust
state_e(e, ctx, ak), if let Expr::If(eg, et, ef) = &e.expr
```

`for`-clauses replace the arg-list relations (`for (pos, earg) in
args.iter().enumerate()`), and `freevar` becomes an ordinary precomputed Rust
function over the tree. The result is markedly shorter and, arguably, closer to
how one would write the analysis by hand.

**Two identities for syntax.** Every node carries a label, and `Eq`/`Hash` are
keyed on the label alone — so a node compares in O(1), like an interned id, and
the labeling chosen at construction decides what "the same expression" means:

* `to_expr` **hash-conses**: structurally equal subterms get the same label
  (and share one allocation). This is exactly the identity Soufflé gives ADT
  values.
* `to_expr_labeled` labels every *occurrence* freshly, recovering the id-based
  analysis' semantics: on **any** term it produces relation-for-relation the
  same results as the flat port (checked at `m = 0/1/2` on duplicate-heavy
  terms in `tests/structured_check.rs`). A labelled AST is the representation
  most hand-written CFA implementations use.

Comparing all three at the same `m` (via `mcfa structured N K P m`):

```text
term N=8 K=2 P=0, m=1        flat (ids)   labelled   hash-consed
  state_e                            65         65            56
  state_a                          4730       4730          4707
  stored_val                       4122       4122          4122
  flow_ee / flow_aa            20 / 576   20 / 576      20 / 576
  total derived                   10769      10769         10714
  time                            37 ms      24 ms         20 ms
```

**Hash-consing is a coarser abstraction.** Identifying structurally equal
subterms is not just deduplication: contexts and addresses are built from
expressions, so two textually identical binding sites anywhere in the program
share a contour entry — structural identity *weakens polyvariance*. Depending
on the term this merges redundant states or cross-wires flows:

* On the worst-case family the repeated `z` references and identity lambdas
  only merge: slightly fewer expression-level facts (`state_e`, `flow_ea`,
  above), identical value-flow (`stored_val`, `flow_ee`, `flow_aa`,
  `copy_ctx`).
* But with two textually identical call sites applied to different closures —
  `(let ((r1 ((lambda (h) (h 0)) f)) (r2 ((lambda (h) (h 0)) g))) …)` — the
  shared `(h 0)` contour at `m = 1` merges the two calls' value addresses,
  cross-wiring `f`'s result into `r2` and `g`'s into `r1`: the hash-consed
  analysis derives strictly *more* `stored_val`/`state_a` facts than the flat
  one (`hashconsing_can_lose_precision` in `tests/structured_check.rs`). At
  `m = 2` the enclosing applications — structurally distinct — re-enter the
  contour and the divergence disappears.

On a term with no duplicate subexpressions the two labelings (and the flat
port) agree exactly, relation-for-relation.

**Cost.** With label-keyed `Eq`/`Hash`, joins and context comparisons are O(1),
and the structured version is as fast as or faster than the flat port (e.g.
`N=10 K=3 P=0, m=1`: flat 771 ms, labelled 739 ms, hash-consed 725 ms — the
hash-consed mode benefits further from having fewer distinct keys).

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

## Is Datalog actually a win? Two hand-written machines

The Datalog program *is* an abstract machine in disguise: `state_e`/`state_a`
are its configurations, `stored_val`/`stored_kont` its (globally widened)
stores, and each rule one case of the transition relation. The crate implements
that machine directly — with no Datalog — twice, at two points on the
naive-to-optimized spectrum. Both run over the labelled syntax and abstract
domains of the structured variant, and `tests/aam_check.rs` checks both derive
**content-identical** relations to the Ascent fixpoint (states, both stores,
and all four `flow_*` relations), on both labelings, at `m = 0/1/2`.

* **The step machine** (`src/aam.rs`) is textbook AAM: a `State` is
  ⟨e, ctx, aκ⟩ or ⟨v, aκ⟩; `step` maps a state to its successors, one `match`
  arm per operational-semantics rule; a worklist runs it to the least fixpoint.
  Two things are not textbook small-step, both forced by the global store:
  *dependency re-firing* (a step that read an address is stale when it grows —
  the engine records readers per address and re-enqueues them; this also
  quietly replaces the Datalog `copy_ctx` standing subscription) and the
  *work-set discipline* (a FIFO, deduplicated queue: a state woken many times
  before it runs steps once, over the batch).
* **The delta worklist** (`src/aam_delta.rs`) is semi-naive evaluation by hand:
  the worklist carries *facts* (a new state, store binding, continuation, copy
  edge), each processed exactly once against the already-known facts on the
  other side of its join, through reverse dependency indices (value address →
  waiting variable reads, continuation address → applied values, context →
  outgoing copy edges). Nothing is ever re-scanned.

Comparing all seven engines at `m = 1`, single thread (`mcfa engines`; "flat"
ports use the appendix's single-id context, the structured ports and machines a
length-`m` vector context; the tuned ports are described below):

| engine | worst-case `N=12 K=3` | church(60) | church(80) |
|--------|----------------------:|-----------:|-----------:|
| ascent (flat, faithful `ascent!`) | 1.01 s | 0.34 s | 0.99 s |
| ascent (flat, tuned) | **0.98 s** | 0.040 s | 0.066 s |
| ascent (flat, generic `ascent_run!`) | 1.97 s | 1.08 s | 3.16 s |
| ascent (structured, labelled) | 1.82 s | 0.75 s | 2.15 s |
| ascent (structured, tuned) | 1.69 s | 0.054 s | 0.094 s |
| AAM (step machine) | 2.09 s | 0.101 s | 0.203 s |
| AAM (delta worklist) | 1.57 s | **0.019 s** | **0.033 s** |

Two very different regimes:

* The **worst-case family is one giant join** — nearly all of its ~585 k facts
  come from the product of `Prim2` continuations × arriving values, over large
  nested `PrimVal` values. Everything lands within ~2×, and the *tuned flat
  Datalog is fastest*: indexed semi-naive joins over interned-id tuples beat
  both hand-written machines at their own game.
* **Church arithmetic is flow propagation** — many rules, small fan-outs, long
  chains. The naive Datalog ports are 1–2 orders of magnitude slower than the
  machines; the delta worklist is fastest overall; and the tuned Datalog closes
  to within ~2–3× of it.

### Why naive Datalog loses on deep terms: frontier-blindness

It is *not* free-variable precomputation — `freevar` is a lower stratum that
the Datalog engines also saturate once (166 iterations, ~8 ms on church(80);
the machines' setup is likewise a few ms).

The diagnosis comes from `MCFA_SUMMARY=1`, which prints Ascent's
`scc_times_summary()` (per-SCC iteration counts, and per-rule times when
`#![measure_rule_times]` is enabled):

* On church(80) the analysis SCC runs **21,273 iterations** deriving 64,334
  facts — **~3 new facts per iteration**. The deep curried structure makes the
  dataflow frontier tiny; the fixpoint crawls, one abstract machine step per
  round. (Worst-case `N=12`: 35 iterations, ~16,700 facts each — wide frontier,
  join work dominates, everything is fine.)
* Per-rule times concentrate almost all of the run in **four rule variants**,
  all with the same shape: the semi-naive variant whose delta is on a *later*
  body atom scans a big `total` index every round:
  - `state_a(v, ak), if if_true(v), stored_kont(ak, ?If{..})` — the guard
    *between* the atoms defeats Ascent's runtime-reorderable simple join, so the
    delta=`stored_kont` variant iterates **all of `state_a`** (`indices_none`)
    each round. Same for the `?Closure` pattern in A-C/cc's first atom.
  - `state_e ⋈ call ⋈ peek_ctx` and `state_e ⋈ var ⋈ stored_val` — 3-atom
    rules: the variant with the delta on the third atom re-enumerates the whole
    2-atom prefix join each round.

  21,273 rounds × O(all states) ≈ quadratic. The delta worklist never rescans:
  its reverse dependency indices mean each new fact touches exactly its
  readers.

The step machine sits in between, and its history makes the same point from
the other side: its first version used a plain LIFO stack with eager wakes (no
dedup), and computed the same fixpoint on the `N=10 K=3` worst-case term in
**83 s** instead of 0.8 s — every hot reader re-scanned its full fan-in once
per arriving tuple. The two lines of worklist folklore (work-*set* dedup, FIFO
batching) are load-bearing; forget them and even naive Datalog wins by 100×.
With them, the step machine's residual cost vs. the delta worklist is batch
re-scanning on re-fires — visible as the ~6× gap on church(80).

### The fix is expressible in the rules (`src/tuned.rs`, `src/structured_tuned.rs`)

`McfaTuned` is the faithful flat port with three mechanical rewrites:

1. **guards/patterns moved after the joins** (`state_a(v, ak),
   stored_kont(ak, ?If{..}), if if_true(v)`) — the two-atom join is then a
   simple join that Ascent evaluates from whichever side is smaller (the delta);
2. **3-atom joins split into binary joins** via intermediate relations
   (`app_state`, `let_state`, `callcc_state`, `var_read`, `copy_edge`) — these
   intermediates *are* the delta worklist's reader indices, materialized as
   relations;
3. **`stored_val`'s address flattened** to columns (`x, ctx, v`) so the store
   joins by key from either side.

`analyze_structured_tuned` applies the same treatment to the structured
(labelled-syntax) port — and needs *less* of it: with syntax carried
structurally, E-Call/E-Let/E-C/cc are already binary `state_e ⋈ peek_ctx`
joins (the syntax match is a guard, not an atom), so only `var_read` and
`copy_edge` are materialized. `tests/tuned_check.rs` verifies both compute the
identical analysis.

The effect on church(80): still ~25 k iterations, but the analysis SCC drops
from 1.02 s to 61 ms (~48 µs/round → ~2.5 µs/round) — ~15× end-to-end, with no
regression on the worst-case term. The residual ~2× vs. the delta worklist is
the irreducible rounds-based dispatch: ~25 k rounds × ~55 rule variants, versus
64 k events each processed once.

**Takeaway.** The machines' advantage was never "Rust vs Datalog" — a worklist
is *frontier-driven by construction*, while semi-naive evaluation is only
frontier-driven if every rule variant can start from its delta. Meeting in the
middle from both directions: the naive-but-clean step machine needs the
work-set folklore just to avoid losing by 100×, the delta worklist that wins
outright is hand-rolled semi-naive whose indices are exactly the tuned port's
intermediate relations, and the tuned Datalog lands within ~2–3× of it while
staying declarative (and winning outright on the join-heavy term). What
Datalog is actually selling is that the safe point on this spectrum is the
*default*: indexing and delta-driven evaluation come for free and degrade
loudly (a slow benchmark) rather than silently (a quadratic worklist that
looks fine on small tests).

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
same identity, and the same effect, as the Rust variant's hash-consed
`to_expr` mode).

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
* As in the appendix, a `let` with no bindings has no evaluation rule —
  `(let () e)` is stuck (none of the term generators produce one).
