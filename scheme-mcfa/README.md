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
4. Adds a **variation**: tunable polyvariance `m` (0/1/2-CFA), reproducing the
   paper's headline observation that too little context makes the analysis
   explode.

## Layout

| File | Contents |
|------|----------|
| `src/lib.rs` | The faithful port of Appendix A. The `ascent!` block's comments name the corresponding operational-semantics / Appendix-A rule. Uses a single-id context `Context{ctx0:id}` exactly as the appendix does (`m = 1`). |
| `src/ast.rs` | The Scheme subset AST, the worst-case term generator (`worst_case_term`), and a feature-exercising term (`feature_term`). |
| `src/edb.rs` | Lowering of the AST to input facts (`Facts`), and a Soufflé `.facts` writer. |
| `src/generic.rs` | **Variation:** the same analysis generalized to a length-`m` contour, with `m` a runtime parameter (`analyze_generic`). |
| `src/main.rs` | CLI runner / benchmark. |
| `souffle/mcfa.dl` | The original Soufflé program, transcribed verbatim from Appendix A (only change: Soufflé 2.4.1 spells the nullary constructor `$MT()`). |
| `tests/cross_check.rs` | Runs Ascent and Soufflé on the same input and asserts the outputs agree. |
| `tests/generic_check.rs` | Checks generic `m=1` ≡ the faithful port, and reproduces the polyvariance/padding phenomena. |

## Running

```bash
# One run of the faithful (m=1) analysis on a worst-case term:
#   N = calls to f, K = nested + applications, P = identity padding
cargo run --release -p scheme-mcfa -- run 10 3 0

# The basic benchmark (a few-second sweep of term sizes):
cargo run --release -p scheme-mcfa -- bench

# The polyvariance variation: run 0/1/2-CFA on the same term:
cargo run --release -p scheme-mcfa -- cfa 8 3 0

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

## Notes

* The faithful port uses the appendix's single-id context, i.e. `m = 1`. The
  `generic` module generalizes this to a bounded length-`m` contour; at `m = 1`
  it produces bit-for-bit the same flow graph as the faithful port (checked in
  `tests/generic_check.rs`).
* Soufflé prints a few "variable occurs once" warnings on `mcfa.dl`; these
  singleton variables are present in the appendix as published and are harmless.
