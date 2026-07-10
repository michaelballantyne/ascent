//! A reduced m-CFA (`var` / 1-ary `lambda` / 1-ary `call` / `if` / `num` /
//! `bool`), at `m = 0` (0-CFA — contexts collapse to `()`), with every
//! syntax node, value, and continuation frame addressed through a Slog-style
//! `Tag(&'static str, usize)` reference instead of `scheme_mcfa::structured`'s
//! `Arc<Node>` (label-keyed `Eq`/`Hash`) or the flat port's per-kind id
//! columns.
//!
//! Cross-checked against `scheme_mcfa::analyze_structured_run(&to_expr_labeled(ast),
//! 0)` on three tiny terms in `tests/slog_style_check.rs`
//! (`mcfa_cross_check_*`): both engines must derive the same number of
//! distinct closure values, and the same variable -> closure-parameter-name
//! bindings. At `m = 0`, `analyze_structured`'s addresses collapse exactly
//! the way this fragment's do (`SAddrV{x, ctx: []}` is keyed by variable name
//! alone; `SAddrK{e, ctx: []}` is keyed by expression alone), so the
//! comparison is apples-to-apples despite the different internal
//! representations.
//!
//! ## Why syntax here is *not* a `relation ID`
//!
//! The obvious "Slog-style" move is `relation ID lam_e(Sym, Tag);` and let
//! the fork mint ids for lambda nodes as they're derived. That's the wrong
//! shape for *input* syntax: `relation ID`'s `!`/auto-inc machinery mints a
//! fresh id only for a **newly-derived, deduplicated** tuple — perfect for
//! `path` in the README's example, which is discovered incrementally with
//! unbounded, provenance-dependent nesting during the fixpoint itself. An
//! AST is not discovered during the fixpoint: every node exists exactly once
//! in the finite input, with an identity already given for free by its
//! position in the source text (exactly what `structured.rs`'s `to_expr_labeled`
//! computes, once, outside Ascent, via a plain counter).
//!
//! Using `relation ID` on syntax anyway actively gets the *wrong* semantics:
//! since a plain relation dedupes on content, `relation ID lam_e(Sym, Tag)`
//! *hash-conses* — two textually distinct occurrences of a structurally
//! identical node (e.g. two `(lambda (w) w)`s) collapse to one id, recovering
//! `to_expr`'s (coarser) identity, not `to_expr_labeled`'s. See
//! `hash_cons_pitfall_probe` for a two-line reproduction of exactly this. So this
//! fragment's syntax relations (`var_e`/`lam_e`/`app_e`/`if_e`/...) carry the
//! occurrence label as an explicit, Rust-assigned column — i.e. exactly the
//! *flat, id-keyed* representation `scheme_mcfa::lib`'s faithful port and
//! `scheme-mcfa/slog/mcfa.slog` already use (mcfa.slog's own "Labelled
//! syntax" section independently arrives at "every node carries a
//! Rust/Slog-program-assigned label" for the identical reason). `relation
//! ID` does not replace that labelling step here; it solves a different
//! problem (minting identity for facts with no a priori position) that this
//! analysis' *syntax* doesn't have.
//!
//! ## Why continuations/values here are plain relations, not `relation ID`
//! rows either
//!
//! The same argument applies one level up. A continuation address in
//! `structured.rs` is `SAddrK { e, ctx }` — a *structural composition* of
//! already-identified things (an expression node, a bounded-length context
//! vector), compared by `Eq`/`Hash` natively; nothing is "discovered" that
//! needs a synthesized handle. At `m = 0` this fragment's continuation
//! address is just the `Tag` of "the sub-expression about to be evaluated" —
//! already unique, already in hand, for free. There is no point in this
//! machine's fixpoint where a *fact itself* (as opposed to the expression or
//! value it's *about*) needs to be referenced from elsewhere by an opaque
//! handle the way `path`'s provenance chain does. I did attempt one
//! continuation kind as a genuine `relation ID` row anyway, to have real
//! (not just argued) evidence either way — see `if_kont_as_id_relation_probe`.
//! It works, but purely mechanically: it adds a join-back through
//! `if_kont_id` everywhere the plain `Kont::If(then, els, ak)` tuple variant
//! would otherwise pattern-match directly, for no offsetting benefit (no
//! sharing, no cheaper equality — `Kont` is already `Eq`/`Hash`-able for
//! free). It is strictly more code to express the same thing.

use ascent::ascent;
use scheme_mcfa::ast::{Ast, Sym};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tag(pub &'static str, pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
   Num(i64),
   Bool(bool),
   /// (param name, body ref) — the closure's "context" is always `()` at m=0,
   /// so there is nothing else to carry.
   Closure(Sym, Tag),
}

pub fn is_truthy(v: &Value) -> bool { !matches!(v, Value::Bool(false)) }

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kont {
   Mt,
   /// evaluating the operator; `(arg ref, next ak)`
   Arg(Tag, Tag),
   /// evaluating the argument, given the (already-evaluated) function
   /// value's *ref* (see `function atomic_eval`'s doc comment below for why
   /// this is a `Tag`, not the `Value` itself); `(func value ref, next ak)`
   Fn(Tag, Tag),
   /// `(then ref, else ref, next ak)`
   If(Tag, Tag, Tag),
}

// ---------------------------------------------------------------------------
// Lowering: Ast -> flat, per-occurrence-labelled relations. This is the
// "flat id-relation" representation (labels assigned by a plain Rust
// counter, exactly `to_expr_labeled`'s scheme, just emitted as relation
// rows instead of an `Arc<Node>` tree) — see the module doc comment for why
// this, and not `relation ID`, is the fragment's syntax representation.
// ---------------------------------------------------------------------------

#[derive(Default)]
pub struct Lowered {
   pub top: Option<Tag>,
   pub var_e: Vec<(usize, Sym)>,
   pub num_e: Vec<(usize, i64)>,
   pub bool_e: Vec<(usize, bool)>,
   pub lam_e: Vec<(usize, Sym, Tag)>,
   pub app_e: Vec<(usize, Tag, Tag)>,
   pub if_e: Vec<(usize, Tag, Tag, Tag)>,
}

fn lower_rec(ast: &Ast, next: &mut usize, l: &mut Lowered) -> Tag {
   let id = *next;
   *next += 1;
   match ast {
      Ast::Var(x) => {
         l.var_e.push((id, x.clone()));
         Tag("var", id)
      },
      Ast::Num(n) => {
         l.num_e.push((id, *n));
         Tag("num", id)
      },
      Ast::Bool(b) => {
         l.bool_e.push((id, *b));
         Tag("bool", id)
      },
      Ast::Lam(params, body) => {
         assert_eq!(params.len(), 1, "mcfa_frag only supports 1-ary lambdas, got {params:?}");
         let body_tag = lower_rec(body, next, l);
         l.lam_e.push((id, params[0].clone(), body_tag));
         Tag("lam", id)
      },
      Ast::App(f, args) => {
         assert_eq!(args.len(), 1, "mcfa_frag only supports 1-ary application, got {} args", args.len());
         let f_tag = lower_rec(f, next, l);
         let a_tag = lower_rec(&args[0], next, l);
         l.app_e.push((id, f_tag, a_tag));
         Tag("app", id)
      },
      Ast::If(g, t, f) => {
         let g_tag = lower_rec(g, next, l);
         let t_tag = lower_rec(t, next, l);
         let f_tag = lower_rec(f, next, l);
         l.if_e.push((id, g_tag, t_tag, f_tag));
         Tag("if", id)
      },
      other => panic!(
         "mcfa_frag: unsupported AST form {other:?} (fragment is var/num/bool/1-ary-lam/1-ary-app/if only)"
      ),
   }
}

pub fn lower(ast: &Ast) -> Lowered {
   let mut l = Lowered::default();
   let mut next = 0usize;
   let top = lower_rec(ast, &mut next, &mut l);
   l.top = Some(top);
   l
}

ascent! {
   pub struct McfaFrag;

   relation top_e(Tag);
   relation var_e(usize, Sym);
   relation num_e(usize, i64);
   relation bool_e(usize, bool);
   relation lam_e(usize, Sym, Tag);
   relation app_e(usize, Tag, Tag);
   relation if_e(usize, Tag, Tag, Tag);

   relation state_e(Tag, Tag);       // (expr ref, continuation address)
   relation state_a(Tag, Tag);       // (value *ref*, continuation address)
   relation stored_val(Sym, Tag);    // m=0: keyed by variable name alone
   relation stored_kont(Tag, Kont);  // continuation address -> frame
   relation value_table(Tag, Value); // value ref -> concrete value (num/bool/lam only; a
                                      // "var" ref always forwards to one of these)

   value_table(Tag("num", *id), Value::Num(*n)) <-- num_e(id, n);
   value_table(Tag("bool", *id), Value::Bool(*b)) <-- bool_e(id, b);
   value_table(Tag("lam", *id), Value::Closure(param.clone(), *body)) <-- lam_e(id, param, body);

   // ---- injection ----
   state_e(t.clone(), t.clone()), stored_kont(t.clone(), Kont::Mt) <-- top_e(t);

   // The demand-driven ("do") version of atomic evaluation (num/bool/lam/var
   // -> value ref), replacing `structured.rs`'s four unconditional `state_a`
   // rules with one `function` declaration + four demand cases. See
   // `atomic_eval_plain` below for the side-by-side eager version.
   //
   // NB: this returns `Tag` (a value *ref*, resolved against `value_table`
   // by whoever consumes it), not `Value` directly. That's a workaround, not
   // a design choice: `function`'s codegen materializes an id-indexed
   // companion for the *answer* relation too (see
   // `ascent_macro::ascent_sugar::desugar_function`'s `res_relation`, which
   // has `need_id: true`) and, for any non-`Copy` return type, uses the
   // bound return variable twice without cloning the second time — a
   // genuine fork bug, not specific to this `Value` type. Minimal repro in
   // `tests/slog_style_check.rs::function_with_non_copy_return_type_is_broken`
   // (`#[ignore]`d, exact rustc error in a comment). Since `Tag` is `Copy`,
   // routing the function through it sidesteps the bug while still
   // genuinely exercising demand-driven dispatch (the `var` case forwards
   // through `stored_val` to whatever ref is actually bound there, which is
   // not simply its own input tag).
   function atomic_eval(Tag) -> Tag;

   state_a(vref.clone(), ak.clone()) <--
      state_e(e, ak), %atomic_eval(e.clone()) -> vref;

   %atomic_eval(?Tag("num", id)) -> vref <-- let vref = Tag("num", *id);
   %atomic_eval(?Tag("bool", id)) -> vref <-- let vref = Tag("bool", *id);
   %atomic_eval(?Tag("lam", id)) -> vref <-- let vref = Tag("lam", *id);
   %atomic_eval(?Tag("var", id)) -> vref <--
      var_e(id, x), stored_val(x, vref0), let vref = *vref0;

   // ---- eager (plain-relation) atomic evaluation, for comparison ----
   relation atomic_eval_plain(Tag, Tag);
   atomic_eval_plain(Tag("num", *id), Tag("num", *id)) <-- num_e(id, _n);
   atomic_eval_plain(Tag("bool", *id), Tag("bool", *id)) <-- bool_e(id, _b);
   atomic_eval_plain(Tag("lam", *id), Tag("lam", *id)) <-- lam_e(id, _param, _body);
   atomic_eval_plain(Tag("var", *id), *vref) <-- var_e(id, x), stored_val(x, vref);

   // ---- if ----
   relation is_false(Tag); // vref points to Value::Bool(false)
   is_false(*vref) <-- value_table(vref, ?Value::Bool(false));

   state_e(g.clone(), g.clone()),
   stored_kont(g.clone(), Kont::If(t.clone(), f.clone(), ak.clone())) <--
      state_e(e, ak), if let Tag("if", id) = e, if_e(*id, g, t, f);

   state_e(t.clone(), ak.clone()) <--
      state_a(vref, akc), stored_kont(akc, ?Kont::If(t, _f, ak)), !is_false(*vref);

   state_e(f.clone(), ak.clone()) <--
      state_a(vref, akc), stored_kont(akc, ?Kont::If(_t, f, ak)), is_false(*vref);

   // ---- call (1-ary) ----
   state_e(fn_ref.clone(), fn_ref.clone()),
   stored_kont(fn_ref.clone(), Kont::Arg(arg_ref.clone(), ak.clone())) <--
      state_e(e, ak), if let Tag("app", id) = e, app_e(*id, fn_ref, arg_ref);

   state_e(arg_ref.clone(), arg_ref.clone()),
   stored_kont(arg_ref.clone(), Kont::Fn(vref.clone(), ak.clone())) <--
      state_a(vref, akf), stored_kont(akf, ?Kont::Arg(arg_ref, ak));

   stored_val(x.clone(), vref_arg.clone()),
   state_e(body.clone(), ak.clone()) <--
      state_a(vref_arg, aka), stored_kont(aka, ?Kont::Fn(vref_fn, ak)),
      value_table(vref_fn, ?Value::Closure(x, body));
}

/// Lowers `ast` and runs [`McfaFrag`] to completion.
pub fn run_frag(ast: &Ast) -> McfaFrag {
   let l = lower(ast);
   let mut prog = McfaFrag::default();
   prog.top_e = vec![(l.top.expect("lower() always sets top"),)];
   prog.var_e = l.var_e;
   prog.num_e = l.num_e;
   prog.bool_e = l.bool_e;
   prog.lam_e = l.lam_e;
   prog.app_e = l.app_e;
   prog.if_e = l.if_e;
   prog.run();
   prog
}

/// Resolves a value ref to its concrete [`Value`], if `vref` is a
/// `num`/`bool`/`lam` ref (a `var` ref never appears as a `value_table` key
/// directly -- it always forwards, via `atomic_eval`/`atomic_eval_plain`, to
/// one of those).
pub fn resolve(prog: &McfaFrag, vref: &Tag) -> Option<Value> {
   prog.value_table.iter().find(|(t, _v)| t == vref).map(|(_t, v)| v.clone())
}

/// `(variable name, bound closure's parameter name)` for every `stored_val`
/// entry that is actually a closure — the thing compared against
/// `scheme_mcfa::structured`'s `stored_val` in the cross-check.
pub fn closure_bindings(prog: &McfaFrag) -> Vec<(Sym, Sym)> {
   let mut out = vec![];
   for (x, vref) in prog.stored_val.iter().cloned() {
      if let Some(Value::Closure(param, _body)) = resolve(prog, &vref) {
         out.push((x, param));
      }
   }
   out
}

/// Every distinct `lam`-kind value ref that is actually reached as a value
/// (via `state_a` or `stored_val`) during the run -- i.e. the number of
/// distinct closures the analysis actually creates, comparable to
/// `analyze_structured`'s distinct `SValue::Closure` count at the same `m`.
pub fn reachable_closure_refs(prog: &McfaFrag) -> std::collections::HashSet<Tag> {
   let mut refs = std::collections::HashSet::new();
   for (vref, _ak) in prog.state_a.iter().cloned() {
      if matches!(vref, Tag("lam", _)) {
         refs.insert(vref);
      }
   }
   for (_x, vref) in prog.stored_val.iter().cloned() {
      if matches!(vref, Tag("lam", _)) {
         refs.insert(vref);
      }
   }
   refs
}

/// The value reaching the top-level (`Kont::Mt`) continuation, if any --
/// i.e. the whole term's result.
pub fn final_result(prog: &McfaFrag) -> Option<Value> {
   let (vref, _ak) = prog.state_a.iter().find(|(_vref, ak)| {
      prog.stored_kont.iter().any(|(k, kv)| k == ak && matches!(kv, Kont::Mt))
   })?;
   resolve(prog, vref)
}

// ---------------------------------------------------------------------------
// Concrete micro-repro: naively spelling syntax as `relation ID` hash-conses
// by content instead of labelling by occurrence.
// ---------------------------------------------------------------------------

ascent! {
   pub struct HashConsPitfall;
   relation raw_var(&'static str);
   relation ID probed_var(Sym);
   >?id.probed_var(scheme_mcfa::ast::sym(x)) <-- raw_var(x);
}

/// Feeds two *occurrences* of the same variable name (as if two distinct
/// `w` leaves appeared in different places in a source term) through a
/// naive `relation ID probed_var(Sym);` and shows they collapse to a single
/// materialized row/id — i.e. `relation ID` used directly on syntax gives
/// `to_expr`'s hash-consed identity, not `to_expr_labeled`'s per-occurrence
/// identity, which is why `mcfa_frag`'s own syntax relations carry an
/// explicit label column instead (see the module doc comment).
pub fn hash_cons_pitfall_probe() -> HashConsPitfall {
   let mut prog = HashConsPitfall::default();
   prog.raw_var = vec![("w",), ("w",)];
   prog.run();
   prog
}

// ---------------------------------------------------------------------------
// A genuine (not just argued) attempt at representing one continuation kind
// as a `relation ID` row addressed by `Tag`, instead of a `Kont` tuple
// variant, to have real evidence for the "adds a join-back, buys nothing"
// claim in the module doc comment.
// ---------------------------------------------------------------------------

/// Alternative `Kont` where the `If` frame is *not* an inline tuple variant
/// but a reference into a `relation ID if_kont_row(...)` table — the direct
/// Slog-style move the task asked to try for continuations.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum KontIdStyle {
   Mt,
   Arg(Tag, Tag),
   Fn(Value, Tag),
   /// `Tag("if_kont", id)` — the frame's actual fields live in
   /// `if_kont_row`/`if_kont_row_id` and must be joined back in.
   IfRef(Tag),
}

ascent! {
   pub struct IfKontAsIdRelation;

   relation top_e(Tag);
   relation if_e(usize, Tag, Tag, Tag);
   // stand-ins so this standalone program typechecks without pulling in the
   // whole fragment; only the `If`-continuation encoding is under test here.
   relation state_e(Tag, Tag);
   relation stored_kont(Tag, KontIdStyle);

   relation ID if_kont_row(Tag, Tag, Tag); // (then ref, else ref, next ak)

   state_e(t.clone(), t.clone()), stored_kont(t.clone(), KontIdStyle::Mt) <-- top_e(t);

   // Creating the continuation: mint an id-relation row, then store a
   // *reference* to it (not the frame itself) in `stored_kont` — this is
   // the extra hop `relation ID` costs relative to `Kont::If(t, f, ak)`.
   let kid = !if_kont_row(t.clone(), f.clone(), ak.clone()),
   if_kont_row_id(t.clone(), f.clone(), ak.clone(), kid),
   state_e(g.clone(), g.clone()),
   stored_kont(g.clone(), KontIdStyle::IfRef(Tag("if_kont", kid))) <--
      state_e(e, ak), if let Tag("if", id) = e, if_e(*id, g, t, f);

   // Using the continuation: cannot pattern-match the frame's fields
   // directly off `stored_kont` (as `?Kont::If(t, _f, ak)` does in
   // `McfaFrag`) — must join back through `if_kont_row_id` first.
   relation if_kont_resolved(Tag, Tag, Tag, Tag); // (frame ref, then, else, next ak)
   if_kont_resolved(Tag("if_kont", *kid), t.clone(), f.clone(), ak.clone()) <--
      if_kont_row_id(t, f, ak, kid);

   relation if_taken(Tag, Tag); // (then ref, next ak) -- reached the then-branch
   if_taken(t.clone(), ak.clone()) <--
      stored_kont(_akc, ?KontIdStyle::IfRef(frame_ref)),
      if_kont_resolved(frame_ref, t, _f, ak);
}

/// Runs [`IfKontAsIdRelation`] on one `if_e` node (`if(cond_id=1, then=Tag("then",10),
/// else=Tag("else",20))`, injected via `top_e`) end to end, to confirm the
/// `relation ID`-addressed continuation actually round-trips (mints a row,
/// stores a ref, joins back through `if_kont_row_id`, and reaches
/// `if_taken`) and not just that it type-checks.
pub fn if_kont_as_id_relation_probe() -> IfKontAsIdRelation {
   let top = Tag("if", 1);
   let mut prog = IfKontAsIdRelation::default();
   prog.top_e = vec![(top,)];
   prog.if_e = vec![(1, Tag("cond", 0), Tag("then", 10), Tag("else", 20))];
   prog.run();
   prog
}
