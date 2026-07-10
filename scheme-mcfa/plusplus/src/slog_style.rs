//! Experiment 2: expressiveness assessment of the plusplus fork's
//! Slog-style features (`relation ID`, `>?id.`, `!` head dependencies,
//! `function`/defunctionalization) against the existing `scheme-mcfa/slog`
//! port and the vanilla-Ascent structured variant.
//!
//! See the doc comment at the bottom of this file (after the code) for the
//! verdict; it's placed after the working examples so it can refer to them
//! concretely. A short pointer up front:
//!
//! - [`baseline`] reproduces the README's edge/path/`Tag`/`path_length`
//!   example (nested-fact ids + defunctionalized function) verbatim enough
//!   to serve as a "the features work at all" smoke test.
//! - [`mcfa_frag`] represents a reduced m-CFA (var/1-ary lambda/1-ary call/if,
//!   `m = 0`) with syntax as flat, Rust-labelled `Tag`-referenced relations
//!   (deliberately *not* `relation ID` — see why in that module's doc
//!   comment), and cross-checks it against `scheme_mcfa::analyze_structured_run`
//!   at `m = 0` on three tiny terms. It also contains two narrower, genuine
//!   attempts at using `relation ID` for values/continuations
//!   (`hash_cons_pitfall_probe`, `if_kont_as_id_relation_probe`), and a
//!   `function`-based demand-driven atomic-eval (`atomic_eval`) alongside an
//!   eager twin (`atomic_eval_plain`) for direct comparison.

pub mod baseline;
pub mod mcfa_frag;

// ---------------------------------------------------------------------------
// Verdict
// ---------------------------------------------------------------------------
//
// (See `tests/slog_style_check.rs` for the executable evidence behind every
// claim below; `cargo test -p scheme-mcfa-plusplus --test slog_style_check`
// — 9 passing, 1 `#[ignore]`d bug repro.)
//
// ## Setup
//
// `baseline` transcribes the README's "Materialization of tuple ID" +
// "Defunctionalization" example (edge/path/`Tag`/`path_length`) as closely as
// possible to the fork's own `ascent_tests/src/provenance.rs::Length` /
// `ascent_macro/src/tests.rs::test_function` — those are the only places in
// the fork's own test suite that exercise `function`/`%`, so treat them as
// closer to "author-blessed" than anything inferable from the README prose
// alone (the README prose and the actual working code disagree in one
// respect — see "Fork semantics, precisely" below).
//
// `mcfa_frag` implements a reduced m-CFA (`Var`/`Lam` (1 param)/`App` (1
// arg)/`If`/`Num`/`Bool`) at `m = 0` (0-CFA: contexts collapse to `()`, so
// `stored_val` is keyed by variable name alone and continuation addresses
// collapse to "the expression currently being evaluated" — no
// `SCtx`/`SAddrK` bookkeeping needed at all). Every syntax node, value, and
// continuation frame is addressed by a `Tag(&'static str, usize)` — a
// generalization of the README's own `Tag("edge", id)`/`Tag("path", id)` to
// six node kinds. **Only the referencing scheme (`Tag`) is Slog-style; the
// *minting* of those tags is a plain Rust counter for syntax, not `relation
// ID`** — see the "why not `relation ID`" sections in `mcfa_frag`'s own doc
// comment for why that turned out to be the right call, backed by a
// concrete two-line repro (`hash_cons_pitfall_probe`) of what goes wrong if
// you use `relation ID` for syntax anyway. I additionally rebuilt one
// continuation kind (`If`) as an honest `relation ID` row
// (`if_kont_as_id_relation_probe`) purely to have real, run, evidence for
// what that costs — not just an argument.
//
// Cross-check: `scheme_mcfa::analyze_structured_run(&to_expr_labeled(&ast),
// 0)` on three hand-built terms restricted to this fragment's forms (no
// `Let`/`Set`/`Callcc`/`Prim`, so both engines process an equivalent term):
// `((lambda (x) x) (lambda (y) y))`, `((lambda (f) (f (lambda (z) z)))
// (lambda (x) x))`, and `(if #t (lambda (a) a) (lambda (b) b))`. At `m = 0`,
// `analyze_structured`'s addresses collapse exactly the same way this
// fragment's do, so the comparison is apples-to-apples despite the
// different internal representations. On all three terms, both engines
// agree exactly on: the number of distinct closures created (2, 3, 1), every
// `(variable, bound closure's parameter name)` pair, and the closure/value
// reaching the top-level continuation. (`tests/slog_style_check.rs`,
// `mcfa_cross_check_*`.)
//
// ## Feature-by-feature verdict
//
// ### `relation ID` / `>?id.` / `.id` (nested-fact ids)
//
// **What it expresses:** mint a fresh, dense integer per distinct
// *newly-derived* tuple, and refer back to "that specific row" from
// elsewhere without carrying its columns as the join key.
//
// **Did it work:** yes, mechanically, exactly as advertised (`baseline`,
// `hash_cons_pitfall_probe`, `if_kont_as_id_relation_probe` all compile and
// run correctly). But it turned out to be the *wrong tool* for both syntax
// and (at `m = 0`) continuations/values in m-CFA, for the same underlying
// reason:
//
// **The problem `relation ID` solves doesn't occur in m-CFA.** `relation
// ID`'s `!`-gated auto-inc mints identity for facts *discovered during the
// fixpoint*, with no smaller pre-existing handle — exactly the README's own
// `path` (a transitive-closure-with-provenance chain: each new derivation is
// a genuinely new witness, unboundedly deep, discovered incrementally).
// Nothing in m-CFA is like that. Syntax is a *finite input*, not discovered
// during the fixpoint — every node already has an identity for free (its
// position in the source text), which is exactly what
// `scheme_mcfa::structured::to_expr_labeled` computes once, outside Ascent,
// via a plain counter. At `m = 0`, continuation/value addresses are just
// that same syntax identity (or, at `m ≥ 1`, a bounded-length *structural
// composition* of syntax identities and prior addresses — still no
// synthesized handle needed, `structured.rs` already gets `Eq`/`Hash` on
// `SAddrK`/`SAddrV` for free). There is simply no point in this analysis
// where a fact *itself* needs an opaque handle the way `path`'s provenance
// chain does.
//
// **Using it anyway gets the *wrong* semantics, concretely.** Since a plain
// relation dedupes by content, `relation ID lam_e(Sym, Tag)` on syntax
// *hash-conses*: `hash_cons_pitfall_probe` feeds two *occurrences* of the
// same variable name through `relation ID probed_var(Sym);` and gets back
// exactly one materialized row/id (`prog.probed_var.len() == 1`), not two —
// recovering `to_expr`'s coarser, structural-equality identity instead of
// `to_expr_labeled`'s per-occurrence one, silently. `mcfa_frag`'s actual
// syntax relations therefore carry the occurrence label as an explicit,
// Rust-assigned column instead (matching `scheme-mcfa/slog/mcfa.slog`'s own
// "every node carries a Slog-program-assigned label" design, arrived at for
// the identical reason).
//
// **It also reintroduces flat-representation friction.** `if_kont_as_id_relation_probe`
// rebuilds one continuation kind (`If`) as a `relation ID if_kont_row(Tag,
// Tag, Tag)` referenced by `Tag("if_kont", id)`. It works
// (`if_kont_as_id_relation_round_trips`), but every site that needs the
// frame's fields must join back through `if_kont_row_id` first — you cannot
// pattern-match `?KontIdStyle::IfRef(..)`'s payload the way `mcfa_frag`'s
// plain `Kont::If(then, els, ak)` tuple variant pattern-matches directly off
// `stored_kont`. This is exactly the "ADT as a lookup key with free
// companion columns degrades to a scan" friction `scheme-mcfa/README.md`
// ("Does representing syntax as ADTs regress Soufflé?") independently
// documents for Soufflé — `relation ID` reintroduces it inside Ascent even
// though Ascent's *own* relation columns don't have that restriction.
//
// **Verdict:** *`relation ID` is real, working sugar for a problem
// (minting identity for facts with no a priori position, discovered
// incrementally during the fixpoint) that this analysis does not have.*
// Applying it anyway is not merely unhelpful but actively regressive: it
// silently swaps per-occurrence identity for hash-consed identity unless you
// route around it with an explicit label column (at which point the feature
// adds nothing), and it reintroduces a join-back-to-see-the-fields cost that
// carrying structured Rust values directly (as `structured.rs` already does)
// doesn't have. Slog needs this because Slog/Soufflé intern structured
// values and have no other handle for "which occurrence"; Rust-embedded
// Ascent already has one (the value itself, or a label field on it).
//
// ### `!` head-clause dependency ("only if new")
//
// **What it expresses:** "generate this second head fact only if the first
// one was *actually newly derived* this round" — an only-if-new propagation
// edge the base semi-naive engine can't otherwise express. `relation ID` and
// `function` are *built on* this (both desugar through a bare `!rel(args)`
// head item — the thing that makes "the size of the relation when this
// tuple was newly generated" a coherent auto-inc counter rather than one
// that ticks up on every re-derivation).
//
// **Verdict:** *I could not construct a place in m-CFA (any `m`) where
// only-if-new propagation is itself the thing needed* — every rule here is
// monotone fact accumulation; nothing depends on whether a specific
// derivation was novel. Every use of `!` I exercised was indirect, via
// `relation ID`/`function`'s desugaring. Not a loss (vanilla Ascent doesn't
// need a replacement because the analysis never asks the question) — just
// orthogonal to this analysis' needs except as plumbing for the other two
// features.
//
// ### `function` / `%f(args) -> ret` (defunctionalization / demand-driven)
//
// **What it expresses:** a magic-sets-style rewrite of "compute f(args)"
// into a demand relation (`f_do`) and an answer relation (`f`), joined by an
// auto-materialized id, generated mechanically from one declaration plus one
// clause per case.
//
// **A genuine fork bug, found while trying to use it for real:**
// `function`'s answer relation is *itself* `relation ID`-shaped
// (`ascent_macro::ascent_sugar::desugar_function`'s `res_relation` has
// `need_id: true`), and for any **non-`Copy` return type**, the generated
// code uses the bound return variable twice without cloning the second time
// — a plain double-move, `error[E0382]`. This is not specific to any type of
// mine: a two-line `function f(usize) -> String;` reproduces it identically
// (minimal repro, `#[ignore]`d, exact rustc output in a comment, in
// `tests/slog_style_check.rs::function_with_non_copy_return_type_is_broken`).
// It is also not cosmetic: rustc's own "help" suggestion (`-> r.clone()`)
// does not parse, because `FunctionCallNode::return_var` is a plain
// `Option<Ident>`, not an `Option<Expr>` — there is no source-level
// workaround for the return *binding* itself. `mcfa_frag::atomic_eval`
// works around this at the design level instead: it returns `Tag` (a
// `Copy` value-*ref*) rather than the `Value` itself, resolving the actual
// value through a separate `value_table` join wherever needed. This sidesteps
// the bug while still genuinely exercising demand dispatch (four cases,
// including one — `var` — that forwards through `stored_val` to a
// dynamically-determined ref, not its own input tag).
//
// **What vanilla Ascent needs instead:** an ordinary relation
// (`atomic_eval_plain`) populated by four unconditional rules — exactly
// `structured.rs`'s four `state_a`-producing rules, and fewer lines than the
// `function` version once the `Copy`-return workaround is factored in.
//
// **Where demand-drivenness actually paid for itself, concretely:** on the
// `if` term (`(if #t (lambda (a) a) (lambda (b) b))`), the else-branch's
// lambda is never reached by any `state_e`, so the demand-driven
// `atomic_eval` never computes an answer for it — while the eager
// `atomic_eval_plain` computes one for *every* `lam_e` row unconditionally,
// reached or not. `function_atomic_eval_is_a_subset_of_eager_atomic_eval_plain`
// checks exactly this: the demand-driven answer set is a *strict* subset of
// the eager one on this term, and merely a subset (not strict — everything
// eager computes is actually reached) on the other two. This is the one
// concrete instance in the whole fragment where demand-drivenness pruned
// real (if here trivial) unreached work — everywhere else in m-CFA, every
// intermediate result semi-naive evaluation reaches is immediately consumed
// by construction, so there's nothing to prune.
//
// **Verdict:** *`function` is a real magic-sets transformation for a
// keyword, and it does what it says — but (a) it has a genuine, sharp bug
// for non-`Copy` return types that this analysis' natural return types
// (`Value`, containing an `Arc<str>`) hit immediately, and (b) even worked
// around, its demand-drivenness only mattered once, on a branch a plain
// eager relation would have wastefully-but-harmlessly computed anyway.*
// Slog's own motivating case (the README's `path_length`) is different in
// kind: there the "function" *is* the entire computation (no larger
// fixpoint bounds what's reachable), so demand-drivenness is the only way to
// avoid computing answers for paths nobody asked about. m-CFA's fixpoint
// already bounds "reachable" tightly (it *is* the AAM's worklist), leaving
// little for a magic-sets rewrite to prune.
//
// ### `va_list` macros
//
// Used only inside `baseline`'s reproduction of the README's own `exists!`/
// `declare_id_rel!` macros (not written by me; transcribed to confirm they
// still parse under this fork rev). Not exercised in `mcfa_frag` — the
// fragment's expression forms don't share enough boilerplate to make a
// `va_list` macro pay for itself over writing out six `relation
// var_e(usize, Sym); relation lam_e(...);` declarations by hand. No verdict
// beyond "still parses".
//
// ## Fork semantics, precisely (undocumented / README-inconsistent details)
//
// - **The non-`Copy`-return `function` bug** (above) — not documented
//   anywhere I found; discovered by trying to return a structured `Value`
//   enum from `atomic_eval` and hitting `error[E0382]` on every case clause.
// - The README's body-suffix example writes `path(y, _).pid` (a bare
//   identifier) to *bind* an id, and separately implies the same syntax
//   filters by an *already-bound* id. In the fork's own working test
//   (`ascent_macro/src/tests.rs::test_function`,
//   `ascent_tests/src/provenance.rs::Length`) the "use an existing bound
//   variable as the id filter" case is spelled `path(x, res).*pid` — a
//   *dereferenced* expression, not a bare identifier — because `?`-pattern
//   destructuring binds by reference and the id-suffix slot parses a full
//   `syn::Expr`, so reusing a by-ref-bound variable there requires an
//   explicit `*`. `baseline` had to discover this by matching the working
//   examples, not the README prose; get it wrong (bare `pid`) and it
//   silently compiles as a *fresh binding* (shadowing) rather than a filter
//   — a sharp, silent edge.
// - `function f(A) -> R;` desugars to *two* `relation ID`s, not one:
//   `f_do(A)` (the demand key, with its own auto-inc id) and `f(usize, R)`
//   (keyed by the *demand's* id, not by `A` itself). Reading off "the answer
//   for key `k`" is therefore a two-hop lookup (`f_do_id` to find `k`'s
//   demand id, then `f` to find that id's answer), not a direct probe on
//   `k` — invisible in the README (which only ever shows the sugared
//   `%f(args) -> ret` spelling) and only surfaced by reading
//   `ascent_macro/src/ascent_sugar.rs::desugar_function`.
