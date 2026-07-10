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
4. Adds three **variations**: tunable polyvariance `m` (0/1/2-CFA), reproducing
   the paper's headline observation that too little context makes the analysis
   explode; a version representing syntax as structured data (a recursive
   enum matched in the rules) rather than flat id-relations, in two labelings —
   hash-consed (structural identity) and per-occurrence (Ascent expresses this
   directly; in Soufflé the obstacle turns out to be ADT *ergonomics*, not join
   cost — see the ADT experiment below); and a version with **no Datalog at
   all** — the same machine hand-written in direct AAM style, checked
   content-identical, benchmarked against the Ascent program.

## Layout

| File | Contents |
|------|----------|
| `src/lib.rs` | The faithful port of Appendix A. The `ascent!` block's comments name the corresponding operational-semantics / Appendix-A rule. Uses a single-id context `Context{ctx0:id}` exactly as the appendix does (`m = 1`). |
| `src/ast.rs` | The Scheme subset AST, the worst-case term generator (`worst_case_term`), and a feature-exercising term (`feature_term`). |
| `src/edb.rs` | Lowering of the AST to input facts (`Facts`), and a Soufflé `.facts` writer. |
| `src/generic.rs` | **Variation:** the same analysis generalized to a length-`m` contour, with `m` a runtime parameter (`analyze_generic`). |
| `src/structured.rs` | **Variation:** syntax represented as a recursive `Expr` enum matched structurally in the rules, instead of flat id-relations (`analyze_structured`). Nodes are labelled: `to_expr` hash-conses (structural identity), `to_expr_labeled` keeps every occurrence distinct (id semantics). |
| `src/aam.rs` | **Variation:** the identical analysis with no Datalog — a hand-written abstract machine (state → state `step`, dependency-tracked worklist) over the same labelled syntax and abstract domains (`analyze_aam`). |
| `src/parallel.rs` | The generic analysis via `ascent_run_par!` (`analyze_generic_par`), for thread-scaling measurements. |
| `src/main.rs` | CLI runner / benchmarks. |
| `souffle/mcfa.dl` | The original Soufflé program, transcribed verbatim from Appendix A (only change: Soufflé 2.4.1 spells the nullary constructor `$MT()`). |
| `souffle/mcfa_adt.dl` | **Experiment:** a Soufflé version that carries syntax as an `expr` ADT instead of flat relations, to test whether ADTs regress performance. |
| `tests/cross_check.rs` | Runs Ascent and Soufflé on the same input and asserts the outputs agree. |
| `tests/generic_check.rs` | Checks generic `m=1` ≡ the faithful port, and reproduces the polyvariance/padding phenomena. |
| `tests/structured_check.rs` | Checks the structured variant against the flat one: the occurrence-labelled tree matches on every term; hash-consing conflates repeated subterms — merging states on some terms, losing precision on others. |
| `tests/aam_check.rs` | Checks the direct abstract machine derives **content-identical** relations (states, stores, flow graph) to the Ascent program, on both labelings, at `m = 0/1/2`. |

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

# The direct (no-Datalog) abstract machine vs. the Ascent program:
cargo run --release -p scheme-mcfa -- aam 10 3 0 1
cargo run --release -p scheme-mcfa -- aam-church 60 1

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

## Is Datalog actually a win? A direct AAM implementation

`src/aam.rs` implements the identical analysis with no Datalog at all, in
textbook AAM style: a `State` is an eval configuration ⟨e, ctx, aκ⟩ or an apply
configuration ⟨v, aκ⟩; `step` maps a state to its successors, one `match` arm
per operational-semantics rule (with the same rule names as the `ascent!`
block); a worklist runs the machine to its least fixpoint. It reuses the
labelled syntax and abstract domains of the structured variant, so the two
engines are directly comparable — `tests/aam_check.rs` checks they derive
**content-identical** relations (states, both stores, and all four `flow_*`
relations), on both labelings, at `m = 0/1/2`.

Two things about the hand-written engine are *not* textbook small-step, both
forced by the global (widened) store:

* **Dependency re-firing.** A step that read a store address is stale if the
  address later grows. The engine records readers per address and re-enqueues
  them on growth — chaotic iteration, ~40 lines. This also quietly replaces the
  Datalog `copy_ctx` relation: there, a flat-closure copy is a *standing*
  subscription (`stored_val(x, to) ⊇ stored_val(x, from)`, forever); here the
  applying state simply re-steps and re-copies when a source address grows.
* **Work-set discipline.** The worklist is FIFO and deduplicated: a state woken
  many times before it runs steps once, over the whole batch. This is what
  stands in for semi-naive evaluation, and it is not optional — see below.

**Benchmarks** (same occurrence-labelled term, `m = 1`, single thread; `mcfa
aam N K P m` / `mcfa aam-church N m`):

| term | Ascent (structured) | direct AAM | |
|------|--------------------:|-----------:|---|
| worst-case `N=10 K=3` | 0.78 s | 0.83 s | join-heavy |
| worst-case `N=12 K=3` | 1.96 s | 2.27 s | |
| church(40) | 0.18 s | 0.035 s | flow-heavy |
| church(60) | 0.76 s | 0.104 s | |
| church(80) | 2.21 s | 0.221 s | (Soufflé: 28.3 s) |

Two regimes, opposite winners:

* The **worst-case family is one giant join**: nearly all of its ~585 k facts
  come from the product of `Prim2` continuations × arriving values. This is
  Datalog's home turf — semi-naive evaluation with hash indices touches each
  delta tuple once — and Ascent is ~15% *faster* than the direct machine, which
  pays for batch re-scans and deep value clones.
* **Church arithmetic is flow propagation**: many rules, small fan-outs, long
  chains. The direct machine is **6–10× faster** here. It dispatches each state
  through one `match`, touching exactly what changed, while the Datalog engine
  pays per-iteration overhead across ~30 rules and maintains indices for every
  relation column it might join on. Re-firing overhead stays small (~7–12%
  extra steps).

And a cautionary tale: this same machine with a plain LIFO stack and eager
wakes (no dedup) computes the same fixpoint on `N=10 K=3` in **83 s** instead
of 0.83 s — every hot reader re-scans its full fan-in once per arriving tuple,
which is quadratic where the join is wide. The two lines of worklist folklore
are load-bearing; forget them and Datalog wins by 100×.

**Takeaway.** For this analysis Datalog's win is not raw speed — a direct
machine of comparable length (~350 lines, and arguably closer to the
operational semantics on the page) matches it on join-heavy adversarial terms
and beats it substantially on realistic higher-order flow. The win is
*robustness*: semi-naive evaluation and indexing come for free and never blow
up asymptotically, whereas the hand-written engine silently degrades by 100×
if the worklist discipline is wrong — and the failure mode (re-scan × fan-in)
is exactly the kind that doesn't show up on small tests.

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
