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
| `mcfa-tuned.slog` | The same analysis restructured for the Slog engine (list access hoisted out of the machine SCC, `var_read`/`copy_edge` reader-index splits, `truthy` inlined) — same output relations, row-for-row. See [Tuning](#tuning-mcfa-tunedslog). |
| `example-arith.slog` | `let`, multi-arg `lambda`, application, `if`, a binary primitive. |
| `example-callcc.slog` | `call/cc` (normal-return path). |
| `example-setbang.slog` | `set!`. |
| `bench-slog.sh` | Benchmark driver: emits the crate's benchmark terms (`mcfa emit-slog`), runs both analysis files under Slog, validates every output relation against the Ascent structured analysis, and reports median fixpoint times. |

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
(`(lambda (x ...) body)` → `(lam L [x ...] body)`). As in the paper, the
`k_fn` continuation carries the argument's integer **position**; the
demand-moded helpers `expr_at`/`param_at` provide the positional list access
(`(expr_at args pos earg)`, `(param_at params pos x)`). A-Ar therefore fires
for **any** operator value and every argument position — non-applicable
operators still get their arguments evaluated, exactly as the paper's rules
do — and A-Call's `param_at` join doubles as the arity filter. (An earlier
draft instead zipped arguments against the callee's parameter names at the
A-Ar step; that under-approximated the paper — no argument evaluation under
non-closure operators, none past the callee's arity, and only the first
argument of an applied continuation.) Small demand-moded helpers (`expr_in`,
`bind_in`, `bind_names`, `expr_at`, `param_at`) enumerate/index these lists;
each is driven in the bound direction by an already-ground list.

## Faithful limitations

The `call/cc` modelling is Appendix A's: the operand may be a closure (applied
to the reified continuation) or a continuation; **invoking a reified
continuation with a non-closure value has no forwarding rule**, so such a path
simply produces no further states (a sound loss of precision). This matches
the crate and the Soufflé program; `example-callcc.slog` therefore exercises
the normal-return path.

## Tuning (`mcfa-tuned.slog`)

The tuned file computes the **identical** analysis (every output relation
row-for-row equal, which `bench-slog.sh` checks on every run); only helper
relations and join shapes change. Three restructurings, chosen for how this
Slog engine evaluates (one fused pipeline per semi-naive rule version,
greedy body scheduling, closed lower-stratum relations read without deltas):

1. **List access hoisted out of the machine SCC.** The faithful port
   indexes argument/parameter/binding lists with demand-moded helpers whose
   ask/answer plumbing lives *inside* the recursive machine stratum. But
   every list the machine touches comes from the program syntax, which is
   fixed — so the tuned file materializes positional tables (`arg_at`,
   `param_at`, `bind_in`, `names_of`) from the syntax subfacts in a lower
   stratum, and the machine SCC reads them as closed relations.
2. **Reader-index splits** (the same `var_read`/`copy_edge` intermediates
   as `src/structured_tuned.rs`): the two triangle joins through the value
   store — variable lookup (`state_e` ⋈ `ref` ⋈ `stored_val`) and the
   flat-closure copy (`copy_ctx` ⋈ `freevar` ⋈ `stored_val`) — are each
   split into two binary joins via a materialized intermediate, so both
   semi-naive delta directions are keyed probes.
3. **`truthy` inlined**: A-IfT is written once per truthy value shape,
   removing a recursive helper relation (and its rule versions) from the
   machine SCC.

## Benchmarking

`bench-slog.sh` ties the two systems together: it emits each benchmark term
as a tiny **loader program** (`mcfa emit-slog-db`, per-occurrence labels —
just the syntax types plus a `(top …)` fact), loads it once per term with
`--out-db`, then runs `mcfa.slog` / `mcfa-tuned.slog` against that saved
database with `-d`. Because the analysis files' own rule text never changes
across terms, their compiled plugins are a cache hit after the very first
time they're ever built — only the term-specific loader recompiles per
term, and it's small. This **validates every output relation's cardinality
against the Ascent structured analysis** on the same term, diffs tuned
against faithful row-for-row, and reports the median summed per-stratum
fixpoint time (the daemon's `(fixpoint …)` lines — pure evaluation,
excluding compile/parse/CSV I/O, comparable to the in-process Ascent
timings from `mcfa engines`).

```sh
SLOG_DIR=/path/to/slog ./bench-slog.sh                  # default sweep
SLOG_DIR=/path/to/slog ./bench-slog.sh "worst 12 3 0"   # one term
```

### Results (median of 3 reps, fixpoint-ms; all relation counts validated
### against Ascent, tuned ≡ faithful row-for-row on every term)

| term | faithful | tuned | tuned speedup |
|---|---|---|---|
| feature | 60.5 | 39.6 | 1.5x |
| worst 8 3 0 | 222.5 | 148.0 | 1.5x |
| worst 12 3 0 | 522.4 | 439.9 | 1.2x |
| church 20 | 9,590 | 6,056 | 1.6x |

Tuning is a modest, consistent win (1.2–1.6x) rather than the dramatic
speedup a single untuned/tuned pair might suggest — see the methodology
note below on why single-run comparisons on this class of workload are
unreliable.

**vs. Ascent** (`mcfa engines`, in-process, best-of-N-engines; both sides
exclude any one-time compile cost):

| term | Slog tuned | Ascent best | ratio |
|---|---|---|---|
| worst 8 3 0 | 148ms | 275ms (flat, tuned) | **Slog ~1.9x faster** |
| worst 12 3 0 | 440ms | 2,242ms (flat, tuned) | **Slog ~5.1x faster** |
| church 20 | 6,056ms | 3.5ms (hand-written AAM delta worklist) | Ascent ~1,700x faster |

Two very different regimes. `worst N 3 0` is *fact-dense per round* — its
main SCC needs only ~90 semi-naive rounds to derive ~500K+ facts (roughly
1,000 facts/round) — and there Slog's parallel, index-planned engine beats
even Ascent's hand-tuned ports outright, with zero manual join ordering.
`church N` is the opposite: its abstract-machine trace is a long,
*sequential* chain (each numeral/fold step depends on the previous one
fully resolving), so its main SCC needs thousands of rounds averaging
**under one new fact per round**. Measured directly (a bare 4,000-step
successor chain, isolated from this analysis entirely): Slog's per-round
floor is ~50µs/round single-threaded and *increases* with thread count on
tiny deltas (3x slower at 4 threads than 1, since partitioning/barrier
overhead has nothing to amortize against); a stratum with 30 dead
co-resident relations costs ~10x more per round than one without them, even
though those relations never derive a single fact — the daemon appears to
pay for every relation's version-rotation and every rule-version's
scheduling once per round, regardless of whether that round's delta touches
them. Ascent's generated Rust loop has none of this fixed cost, so it
absorbs thousands of nearly-empty rounds for microseconds each, while
Slog's bulk-superstep design — built to amortize over large deltas — pays
its setup cost thousands of times over. This is a workload-shape
mismatch, not a defect in the m-CFA encoding: the same rules that make Slog
competitive-to-better on `worst` make it look bad on `church`.

**Known ceiling:** terms are compiled as literal Slog facts (there is no
CSV/binary-import bypass in this toolchain — confirmed by reading the
compiler; `--out-db`/`-d` only saves what a compiled program derived, it
doesn't accept raw input). Slog's front end does not scale gracefully past
roughly 1,000–2,000 distinct interned syntax nodes for a recursive
structured value: `church 40` (1,834 nodes) and `church 80` (6,834 nodes)
both fail to compile within minutes — one hangs in the Racket-side join
planner, the other in C++ codegen — regardless of whether the term is
inlined with the analysis or split into its own loader file. `church 20`
(534 nodes) and `worst 12 3 0` are the largest terms exercised here.

**Methodology caveats, found the hard way:** this container's timing
proved noisy enough that single runs disagreed with each other by up to
5x with no code changes; a stale-cache interaction between the inline and
staged input methods produced genuine (reproducible, not transient)
`undefined symbol` plugin-load crashes that an earlier version of this
script silently mistook for successful-but-fast runs (summing only the
`(fixpoint …)` lines printed before the crash). `bench-slog.sh` now retries
a rep on that failure signature rather than accepting a truncated log; the
table above is from a from-scratch build-cache clear, 3 clean serial reps,
zero crashes. Treat the ratios above as reliable to about ±20%, not as
precise multipliers — and treat any *single*-run comparison on this class
of workload (few-fact-per-round, thousands of rounds) with real suspicion.

