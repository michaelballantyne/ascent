# `slog/` — *m*-CFA for Scheme, ported to Slog

A port of this crate's control-flow analysis to
[Slog](https://github.com/harp-lab/slog-lang1) (a parallel, JIT-compiled
Datalog with first-class structured values and demand-driven relations).

It is the third representation of the same analysis in this crate:

| representation | syntax carried as | file |
|---|---|---|
| flat id-relations (faithful to the paper's Appendix A) | `lambda`/`call`/`if`/… input relations keyed by node id | `../src/lib.rs`, `../souffle/mcfa.dl` |
| structured data (Ascent) | a recursive `Expr` enum, matched in rules | `../src/structured.rs` |
| **structured data (Slog)** | **a recursive `expr` union value, matched in rules** | **`mcfa.slog`** |

This port follows the **structured** variant: syntax is a recursive
structured value matched on directly, exactly as the value and continuation
ADTs are — no flat id-relations. Concretely it corresponds to
`structured.rs`'s **`to_expr_labeled`** (per-occurrence) identity (see
[Labelled syntax](#labelled-syntax)).

## Files

| File | Contents |
|------|----------|
| `mcfa.slog` | The whole analysis: syntax/value/continuation `union`s, the negation-free `freevar`, and every machine rule. `include` it. |
| `example-arith.slog` | `let`, multi-arg `lambda`, application, `if`, a binary primitive. |
| `example-callcc.slog` | `call/cc` (normal-return path). |
| `example-setbang.slog` | `set!`. |

## Running

Slog compiles a program to a native plugin and runs it under its fixpoint
engine, writing one CSV per relation to the `--debug-dir`. From the Slog
repository root:

```sh
racket slog.rkt --debug-dir out/arith   /path/to/ascent/scheme-mcfa/slog/example-arith.slog
racket slog.rkt --debug-dir out/callcc  /path/to/ascent/scheme-mcfa/slog/example-callcc.slog
racket slog.rkt --debug-dir out/setbang /path/to/ascent/scheme-mcfa/slog/example-setbang.slog
```

`include "mcfa.slog"` resolves relative to the example file, so the examples
can live outside the Slog tree. Sample results (`out/<ex>/result.csv`):

| example | `result` |
|---|---|
| arith   | `(v_prim "+" (v_prim "+" (v_num 1) (v_num 2)) (v_num 10))` |
| callcc  | `(v_prim "+" (v_num 1) (v_num 2))` |
| setbang | `(v_num -42)` |

Other relations of interest: `flow_ea` (expression → value), `stored_val`
(the abstract value store), `freevar`, `state_e`/`state_a` (reachable
machine states), `stored_kont` (the continuation store).

## The analysis

A demand-free small-step **abstract abstract machine** (AAM): a CESK\*-style
machine with a value store `stored_val` and a continuation store
`stored_kont`, made finite by *m*-CFA polyvariance with **m = 1** — a
context (`ctx`) is the single most-recent binding site. Two relations drive
it: `state_e e ctx ak` ("evaluate `e`") and `state_a v ak` ("value `v` is
ready for continuation `ak`"). Every reachable state and store binding is a
fact; the fixpoint terminates because the abstract state space is finite.

Each Slog rule mirrors one rule of `souffle/mcfa.dl` / `structured.rs`:

| machine step | Slog rule(s) |
|---|---|
| injection | `rule (top e) --> …` |
| context creation (`peek_ctx`) | the four `state_e … --> (peek_ctx …)` rules |
| flat-env free-var copy (`copy_ctx`) | `rule (copy_ctx …) (freevar …) (stored_val …) --> …` |
| E-If / E-C/cc / E-Set! / E-Call / E-Let / E-Prim | the `state_e … = (if_e/callcc/set_e/app/let_e/prim …)` rules |
| atomic eval (num/bool/lam/var) | the four `state_e … --> (state_a …)` rules |
| A-IfT / A-IfF / A-C/cc / A-C/ccKont / A-Ar / A-Call / A-Let / A-Prim1/2 / A-Set! | the `state_a … (stored_kont ak …) --> …` rules |

## Slog adaptations

Three things differ from a mechanical transcription, each forced by a Slog
feature (or its absence):

### Labelled syntax

Slog **interns** structured values, so two textually identical subterms are
the *same* value — the identity of `structured.rs`'s hash-consed `to_expr`.
To instead match `to_expr_labeled` (each *occurrence* distinct, agreeing with
the flat id-based analysis), **every `expr` node carries a unique integer
label as its first field** (`(ref 8 "t")`, `(lam 2 ["a" "b"] …)`, …). Because
contexts, closures, and addresses are built from these labelled nodes,
polyvariance is occurrence-sensitive. The label's *value* is never inspected
— it is matched with `_` in every rule; it exists only to keep occurrences
apart, and the input program assigns it. (Verified: two identical
`(lambda (w) w)` occurrences with distinct labels yield two distinct closures,
where hash-consing would merge them.)

### Negation-free `freevar`

`structured.rs` precomputes free variables in Rust; the Soufflé version uses
stratified negation (`!lambda_arg_list(vars, _, x)`). **Slog has no
negation**, so `freevar` is computed here by rules, with the binder filter
written positively: a variable is free in a `lambda` when it is free in the
body and `(lmem params x) < 1` — i.e. absent from the parameter list. Nodes
are enumerated by Slog's **subfact closure** (every subterm of a fact is a
fact), the same mechanism the tinycfa `freevars.slog` example relies on. The
paper's quirk that a `let` *body* is not scoped by the bound names is
preserved.

### Multi-argument application over lists

Multi-argument `lambda`/`app` and multi-binding `let` carry Slog lists
(`(lambda (x ...) body)` → `(lam L [x ...] body)`). Rather than the paper's
positional `Fn{…, pos, …}` continuation indexing a parameter list by integer,
the `k_fn` continuation carries the **parameter name** being bound, obtained
by zipping the argument list against the callee's parameter list at the A-Ar
step (`zip2`). This is equivalent and avoids positional list access. Small
demand-moded helpers (`expr_in`, `bind_in`, `bind_names`, `zip2`) enumerate /
zip these lists; each is driven in the bound direction by an already-ground
list.

## Faithful limitations

The `call/cc` modelling is Appendix A's: the operand may be a closure (applied
to the reified continuation) or a continuation; **invoking a reified
continuation with a non-closure value has no forwarding rule**, so such a path
simply produces no further states (a sound loss of precision). This matches
the crate and the Soufflé program; `example-callcc.slog` therefore exercises
the normal-return path.
