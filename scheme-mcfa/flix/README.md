# `flix/` — *m*-CFA for Scheme, ported to Flix's first-class Datalog

A port of this crate's control-flow analysis to
[Flix](https://flix.dev/) (measured with Flix **0.75.1** built from source;
the Datalog engine is the built-in **Fixpoint3** solver — first-class Datalog
program values embedded in a typed functional language).

| file | contents |
|---|---|
| `mcfa.flix` | the straightforward port: enums for values/addresses, the rule set as one `#{...}` Datalog value, a TSV facts loader, and a timing/reporting `main`. |
| `mcfa_tuned.flix` | the delta-friendly rewrite (materialized redex relations, shadow decomposition relations) — see below. |
| `run.sh` | wrapper: `./run.sh FACTSDIR` (set `FLIX_JAR` to override the jar path). |

## Running

```bash
# emit a term's input facts (same TSV .facts files the Soufflé port reads):
cargo run --release -p scheme-mcfa -- emit-flix /tmp/facts worst 8 3 0

# compile + run (compilation is ~25-40 s of the wall time):
java -Xmx8g -jar flix.jar mcfa.flix -- /tmp/facts

# expected sizes, for cross-checking:
cargo run --release -p scheme-mcfa -- expected worst 8 3 0
```

The program prints `solve1`/`solve2` (cold and warm-JIT fixpoint times, ms)
and then one `relation count` line per output relation, in the same format
as `mcfa expected`.

## The port: what Flix's Datalog fragment forces

Flix is the *most restrictive* host so far, and the restrictions are
load-bearing for the story this crate tells:

* **Body atoms may contain only variables, wildcards, and primitive
  constants** — no enum or tuple destructuring (error E4809). The paper's
  `stored_kont(ak, $If(et, ef, ctx, ak'))` cannot be written. So the
  continuation store becomes **one relation per `Kont` variant**
  (`KontIf(ak, et, ef, ctx, nak)`, `KontArg(...)`, ... — the variant tag
  promoted into the relation name), and the value store is **flattened into
  columns** (`StoredVal(x, ctx, v)`). These are *exactly* the rewrites the
  tuned Ascent (`src/tuned.rs`) and tuned Soufflé (`souffle/mcfa_tuned.dl`)
  ports needed by hand to become delta-friendly — Flix's type discipline
  forces the fast schema from day one. (What it cannot force is rule-level
  delta-friendliness; see the tuning section.)
* **Values still need *some* destructuring** (A-Call must take a
  `VClosure(elam, ctx)` apart to find the callee's lambda). Flix's
  *functional predicates* — `let (elam, ctxclo) = closureParts(v)` where the
  helper returns a `Vector` (empty ⇒ the rule is filtered out) — play the
  role of Ascent's `if let` patterns, and read rather nicely.
* **Stratified negation exists** (unlike egglog and Slog), so `freevar` is
  computed in-language, like the Soufflé original. Two accommodations:
  negated atoms admit no wildcards, so the two `!lambda_arg_list(vars,_,x)`
  literals are projected through helper relations (`IsParam`, `LetBound`)
  first.
* **Head terms are full expressions**, so constructing addresses and values
  in heads (`KontIf(AddrK.KAddr(eguard, ctx), ...)`) works exactly like the
  Soufflé original.
* Soufflé's multi-head rules have no Flix analogue: the straightforward port
  duplicates the body per head (3–4× re-evaluation), which the tuned version
  undoes with materialized redex relations.
* The `m = 1` context is just a `String` type alias (the binding-site id) —
  with no ADT matching in bodies there is no reason to wrap it.

**Correctness.** All eleven output counts (including in-language `freevar`)
match the Ascent fixpoint exactly on the feature term, `worst 4 2 0`,
`church 10`, `church 30`, `worst 8 3 0`, `worst 12 3 0`, and `church 60`.

## Two Flix findings the port surfaced

1. **A soundness bug in Fixpoint3 (Flix 0.75.1).** A variable bound by a
   functional predicate, when used as an *argument of a later body atom*, is
   not join-constrained: `A(v), let x = f(v), B(x, y)` matches every row of
   `B`, not just those with key `x` (minimal repro confirmed outside this
   program). The straightforward port works around it by binding a fresh
   variable in the atom and comparing with a guard
   (`Lambda(elam0, ...), if (elam0 == elam)`) — correct, but it turns an
   indexed join into a scan of every lambda per match. The tuned version
   sidesteps the bug entirely (shadow decomposition relations use
   functional-predicate outputs only in heads, which is safe).
2. **Timing pure code is adversarial.** `solve` is pure, so the optimizer
   inlines a once-used solve into its single use site — and a `query`
   evaluates only the strata its selected predicate needs. A naive
   `t0; solve; t1` sandwich measures 0 ms while the real work happens at
   the first query of a derived relation. The driver forces each timed model
   through queries on two relations (one of them a stratification sink)
   before reading the clock. Worth knowing before benchmarking anything
   Flix-shaped.

## Performance

Same machine and terms as the crate README's engine table. "Flix" rows are
the in-process cold `solve1` fixpoint time (excluding JVM startup, the
~30 s compile, and fact loading; a warm second solve is ~10% faster);
Ascent/AAM are in-process; egglog is whole-process (parse/load ≤ 0.5 s):

| engine (single thread) | worst `N=8 K=3` | worst `N=12 K=3` | church(30) | church(60) | church(80) |
|---|---:|---:|---:|---:|---:|
| ascent (flat, tuned) | 0.25 s | 1.45 s | 0.022 s | 0.089 s | 0.137 s |
| AAM (delta worklist) | 0.27 s | 2.09 s | 0.006 s | 0.026 s | 0.044 s |
| egglog | 0.10 s | 0.63 s | 0.81 s | 3.5 s | 7.0 s |
| **Flix (straightforward)** | 3.7 s | 19.4 s | 25.4 s | 280 s | — (not run) |
| **Flix (tuned)** | 3.3 s | 17.6 s | 11.5 s | 70.8 s | 173 s |

* The **tuned rewrite pays only in the flow-propagation regime**: 2.2× on
  church(30), 4.0× on church(60) — eliminating the 3–4× multi-head body
  re-evaluation and the guarded `Lambda` scans is real — but ~nothing on the
  worst-case terms, whose cost is carrying 250 k+ tuples of deeply-nested
  `Value` enums through the solver, not join re-evaluation.
* The **residual gap is engine-level, not rule-level**: tuned Flix is still
  ~800× tuned Ascent on church(60), and diagnostics bound rule-shape
  suspects tightly — dropping all four `flow_*` relations moves ~10%,
  dropping the whole `freevar` stratum plus the copy rules moves ≤25%.
  Fixpoint3 interprets a compiled relational-algebra machine over persistent
  B+-trees of boxed, `Order`-compared enum values; every per-tuple constant
  is a multiple of what Ascent's specialized `HashMap` indices or egglog's
  interned u32 ids pay. (Flix's `--threads` flag controls compiler threads,
  not the solver, so no thread-scaling numbers.)
* Superlinear scaling in the Church family compounds it: naive Flix goes
  25 s → 280 s from church(30) to church(60) (11× for 3.6× the facts),
  suggesting per-iteration work that scans more than the frontier — the
  same frontier-blindness the crate README diagnoses in naive Ascent, at
  ~1000× the constant factor.

## Notes / gotchas (Flix 0.75.1)

* A single `def` holding the whole ~30-relation rule set plus driver
  overflows the JVM's 64 KB method-bytecode limit ("Method too large") —
  the rule set lives in its own `def rules(): #{...}` with the full
  row-polymorphic schema type spelled out (top-level `def`s require explicit
  types).
* A Datalog body variable that shadows an outer lexical `let` is silently
  treated as a *constant* (the captured value), not a fresh logic variable —
  renaming the CLI-args binding away from `args` fixed a wrong `Freevar`.
* `query` returns *sets* of the selected tuples — selecting a projection of
  a relation's columns deduplicates; count relations by selecting every
  column.
* `query`'s `from` clause is a single atom (no joins/guards) — post-filter
  the returned `Vector` instead.
* `inject` into an arity-1 relation takes bare elements, not 1-tuples.
* Effects must be fully qualified (`\ {IO, Fs.FileRead.FileRead, ...}`), and
  file reading via `Fs.FileRead.readLines` needs no explicit handler under
  `IO` (default handlers).
