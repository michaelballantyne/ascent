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
| `src/main.rs` | CLI runner / benchmark. |
| `souffle/mcfa.dl` | The original Soufflé program, transcribed verbatim from Appendix A (only change: Soufflé 2.4.1 spells the nullary constructor `$MT()`). |
| `tests/cross_check.rs` | Runs Ascent and Soufflé on the same input and asserts the outputs agree. |
| `tests/generic_check.rs` | Checks generic `m=1` ≡ the faithful port, and reproduces the polyvariance/padding phenomena. |
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

## Notes

* The faithful port uses the appendix's single-id context, i.e. `m = 1`. The
  `generic` module generalizes this to a bounded length-`m` contour; at `m = 1`
  it produces bit-for-bit the same flow graph as the faithful port (checked in
  `tests/generic_check.rs`).
* Soufflé prints a few "variable occurs once" warnings on `mcfa.dl`; these
  singleton variables are present in the appendix as published and are harmless.
