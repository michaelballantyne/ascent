//! **Variation: syntax as structured data.**
//!
//! The paper's Appendix A represents *values* and *continuations* as Soufflé
//! ADTs, but flattens *syntax* into id-keyed input relations (`lambda`, `call`,
//! `if`, `let`, `var`, ...) that rules join on by expression id. As the paper's
//! own choice of "much more verbose" phrasing hints, ADTs are used sparingly:
//! Soufflé indexes/joins on ADTs poorly, so driving control flow by *matching
//! on recursive syntax* would be impractical there.
//!
//! Ascent has no such restriction — a relation column can be any
//! `Clone + Eq + Hash` value, and rule bodies can pattern-match it — so we can
//! represent syntax the same way the paper represents values and continuations:
//! as a recursive [`Expr`] enum. The flat `lambda`/`call`/`if`/... relations
//! disappear entirely; every rule instead matches on the structure of the
//! expression in the current `state_e`.
//!
//! ## Semantic note
//!
//! Because expressions are compared *structurally* (like the value ADTs),
//! structurally-identical subterms are identified. This differs from the
//! id-based port, where each syntactic *occurrence* is distinct. On terms with
//! no duplicate subexpressions the two agree exactly (see
//! `tests/structured_check.rs`); on terms with repeated subterms the structured
//! version conflates them (fewer, merged facts). Occurrence-sensitivity could
//! be recovered by labelling nodes (keying `Eq`/`Hash` on a per-node id while
//! still storing children inline) — a labelled AST — which we discuss in the
//! crate README.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::Arc;

use ascent::ascent_run;

use crate::ast::{Ast, Sym};

/// Recursive syntax, carried directly as structured data in relations.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Expr {
   Var(Sym),
   Num(i64),
   Bool(Sym), // "#t" / "#f"
   Lam(Vec<Sym>, E),
   App(E, Vec<E>),
   If(E, E, E),
   Let(Vec<(Sym, E)>, E),
   Set(Sym, E),
   Callcc(E),
   Prim(Sym, E, E),
}

/// A (shared) expression.
pub type E = Rc<Expr>;

/// Convert the surface [`Ast`] into a structured [`Expr`] tree.
pub fn to_expr(ast: &Ast) -> E {
   Rc::new(match ast {
      Ast::Var(x) => Expr::Var(x.clone()),
      Ast::Num(n) => Expr::Num(*n),
      Ast::Bool(b) => Expr::Bool(Arc::from(if *b { "#t" } else { "#f" })),
      Ast::Lam(ps, b) => Expr::Lam(ps.clone(), to_expr(b)),
      Ast::App(f, args) => Expr::App(to_expr(f), args.iter().map(to_expr).collect()),
      Ast::If(g, t, f) => Expr::If(to_expr(g), to_expr(t), to_expr(f)),
      Ast::Let(bs, b) => {
         Expr::Let(bs.iter().map(|(x, e)| (x.clone(), to_expr(e))).collect(), to_expr(b))
      }
      Ast::Set(x, e) => Expr::Set(x.clone(), to_expr(e)),
      Ast::Callcc(e) => Expr::Callcc(to_expr(e)),
      Ast::Prim(op, a, b) => Expr::Prim(op.clone(), to_expr(a), to_expr(b)),
   })
}

/// `context` — the most-recent (up to) `m` binding-site expressions.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SCtx(pub Vec<E>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SAddrK { pub e: E, pub ctx: SCtx }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SAddrV { pub x: Sym, pub ctx: SCtx }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SValue {
   Number(i64),
   Bool(Sym),
   Kont(SAddrK),
   Closure { e: E, ctx: SCtx },
   PrimVal { op: Sym, v1: Box<SValue>, v2: Box<SValue> },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SKont {
   MT,
   Arg { args: Vec<E>, ctx: SCtx, ectx: SCtx, next_ak: SAddrK },
   Fn { func: SValue, pos: i64, ctx: SCtx, next_ak: SAddrK },
   Set { loc: SAddrV, next_ak: SAddrK },
   If { true_branch: E, false_branch: E, ctx: SCtx, next_ak: SAddrK },
   Callcc { ectx: SCtx, next_ak: SAddrK },
   Let { av: SAddrV, ebody: E, ctx: SCtx, next_ak: SAddrK },
   Prim1 { op: Sym, e2: E, ctx: SCtx, next_ak: SAddrK },
   Prim2 { op: Sym, v1: SValue, next_ak: SAddrK },
}

fn sextend(e: &E, old: &SCtx, m: usize) -> SCtx {
   if m == 0 {
      return SCtx(Vec::new());
   }
   let mut v = Vec::with_capacity(m);
   v.push(e.clone());
   v.extend(old.0.iter().take(m - 1).cloned());
   SCtx(v)
}

fn sif_true(v: &SValue) -> bool {
   matches!(v, SValue::Closure { .. } | SValue::Number(_) | SValue::Kont(_))
      || matches!(v, SValue::Bool(b) if b.as_ref() == "#t")
}

/// Free variables of every subexpression, computed exactly as the paper's
/// `freevar` relation does (note: `set!`'s target variable is not counted as
/// free, and a `let` body is *not* scoped by the let-bound names — both faithful
/// to Appendix A). Memoized over structurally-equal subterms.
fn free_vars(e: &E, cache: &mut HashMap<E, Rc<Vec<Sym>>>) -> Rc<Vec<Sym>> {
   if let Some(v) = cache.get(e) {
      return v.clone();
   }
   let set: BTreeSet<Sym> = match &**e {
      Expr::Var(x) => std::iter::once(x.clone()).collect(),
      Expr::Num(_) | Expr::Bool(_) => BTreeSet::new(),
      Expr::Lam(ps, b) => {
         let bound: BTreeSet<&Sym> = ps.iter().collect();
         free_vars(b, cache).iter().filter(|x| !bound.contains(x)).cloned().collect()
      }
      Expr::App(f, args) => {
         let mut s: BTreeSet<Sym> = free_vars(f, cache).iter().cloned().collect();
         for a in args {
            s.extend(free_vars(a, cache).iter().cloned());
         }
         s
      }
      Expr::Prim(_, a, b) => {
         let mut s: BTreeSet<Sym> = free_vars(a, cache).iter().cloned().collect();
         s.extend(free_vars(b, cache).iter().cloned());
         s
      }
      Expr::If(g, t, f) => {
         let mut s: BTreeSet<Sym> = free_vars(g, cache).iter().cloned().collect();
         s.extend(free_vars(t, cache).iter().cloned());
         s.extend(free_vars(f, cache).iter().cloned());
         s
      }
      Expr::Set(_x, ev) => free_vars(ev, cache).iter().cloned().collect(),
      Expr::Callcc(ev) => free_vars(ev, cache).iter().cloned().collect(),
      Expr::Let(binds, body) => {
         let bound: BTreeSet<&Sym> = binds.iter().map(|(x, _)| x).collect();
         let mut s: BTreeSet<Sym> = BTreeSet::new();
         for (_, be) in binds {
            s.extend(free_vars(be, cache).iter().filter(|x| !bound.contains(x)).cloned());
         }
         // NB: the let body is intentionally *not* scoped, matching the paper.
         s.extend(free_vars(body, cache).iter().cloned());
         s
      }
   };
   let r = Rc::new(set.into_iter().collect::<Vec<_>>());
   cache.insert(e.clone(), r.clone());
   r
}

/// Relation sizes from a structured-syntax run.
#[derive(Clone, Debug, Default)]
pub struct StructuredStats {
   pub m: usize,
   pub state_e: usize,
   pub state_a: usize,
   pub stored_val: usize,
   pub stored_kont: usize,
   pub flow_ee: usize,
   pub flow_ea: usize,
   pub flow_ae: usize,
   pub flow_aa: usize,
   pub peek_ctx: usize,
   pub copy_ctx: usize,
}

impl StructuredStats {
   pub fn total_derived(&self) -> usize {
      self.state_e + self.state_a + self.stored_val + self.stored_kont
         + self.flow_ee + self.flow_ea + self.flow_ae + self.flow_aa
   }
}

/// Run `m`-CFA on a structured [`Expr`], driving control flow by matching on
/// syntax rather than joining flat id-relations.
pub fn analyze_structured(top: &E, m: usize) -> StructuredStats {
   let empty = SCtx(Vec::new());

   // Precompute free variables (the only place the paper uses `freevar`).
   let mut cache: HashMap<E, Rc<Vec<Sym>>> = HashMap::new();
   free_vars(top, &mut cache);
   let fvs = cache;

   let prog = ascent_run! {
      relation top_expr(E) = vec![(top.clone(),)];

      relation state_e(E, SCtx, SAddrK);
      relation state_a(SValue, SAddrK);
      relation stored_val(SAddrV, SValue);
      relation stored_kont(SAddrK, SKont);
      relation flow_ee(E, E);
      relation flow_ea(E, SValue);
      relation flow_aa(SValue, SValue);
      relation flow_ae(SValue, E);
      relation peek_ctx(E, SCtx, SCtx);
      relation copy_ctx(SCtx, SCtx, E);

      // injection of the top expression
      state_e(top.clone(), empty.clone(), SAddrK { e: top.clone(), ctx: empty.clone() }),
      peek_ctx(top.clone(), empty.clone(), sextend(top, &empty, m)),
      stored_kont(SAddrK { e: top.clone(), ctx: empty.clone() }, SKont::MT) <--
         top_expr(top);

      // peek_ctx: contexts are created only at binding forms
      peek_ctx(e.clone(), old.clone(), sextend(e, old, m)) <--
         state_e(e, old, _),
         if matches!(&**e, Expr::App(..) | Expr::Let(..) | Expr::Callcc(..) | Expr::Lam(..));

      // copy_ctx: copy the free-variable bindings between contexts
      stored_val(SAddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
         copy_ctx(from, to, e),
         for fv in fvs.get(e).unwrap().iter(),
         stored_val(SAddrV { x: fv.clone(), ctx: from.clone() }, v);

      // E-If
      state_e(eg.clone(), ctx.clone(), SAddrK { e: eg.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: eg.clone(), ctx: ctx.clone() },
                  SKont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), eg.clone()) <--
         state_e(e, ctx, ak), if let Expr::If(eg, et, ef) = &**e;

      // E-C/cc
      state_e(elam.clone(), ctx.clone(), SAddrK { e: elam.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: elam.clone(), ctx: ctx.clone() },
                  SKont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), elam.clone()) <--
         state_e(e, ctx, ak), if let Expr::Callcc(elam) = &**e, peek_ctx(e, ctx, ectx);

      // E-Set!
      state_e(esub.clone(), ctx.clone(), SAddrK { e: esub.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: esub.clone(), ctx: ctx.clone() },
                  SKont::Set { loc: SAddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
      flow_ee(e.clone(), esub.clone()) <--
         state_e(e, ctx, ak), if let Expr::Set(x, esub) = &**e;

      // E-Call
      state_e(efunc.clone(), ctx.clone(), SAddrK { e: efunc.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: efunc.clone(), ctx: ctx.clone() },
                  SKont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), efunc.clone()) <--
         state_e(e, ctx, ak), if let Expr::App(efunc, eargs) = &**e, peek_ctx(e, ctx, ectx);

      // E-Let
      state_e(ebnd.clone(), ctx.clone(), SAddrK { e: ebnd.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: ebnd.clone(), ctx: ctx.clone() },
                  SKont::Let { av: SAddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
      copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
      flow_ee(e.clone(), ebnd.clone()) <--
         state_e(e, ctx, ak),
         if let Expr::Let(binds, ebody) = &**e,
         peek_ctx(e, ctx, ectx),
         for (x, ebnd) in binds.iter();

      // E-Prim
      state_e(e0.clone(), ctx.clone(), SAddrK { e: e0.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: e0.clone(), ctx: ctx.clone() },
                  SKont::Prim1 { op: op.clone(), e2: e1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), e0.clone()) <--
         state_e(e, ctx, ak), if let Expr::Prim(op, e0, e1) = &**e;

      // atomic evaluation
      state_a(SValue::Number(*n), ak.clone()),
      flow_ea(e.clone(), SValue::Number(*n)) <--
         state_e(e, _, ak), if let Expr::Num(n) = &**e;

      state_a(SValue::Bool(b.clone()), ak.clone()),
      flow_ea(e.clone(), SValue::Bool(b.clone())) <--
         state_e(e, _, ak), if let Expr::Bool(b) = &**e;

      state_a(SValue::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
      flow_ea(e.clone(), SValue::Closure { e: e.clone(), ctx: ctx.clone() }) <--
         state_e(e, ctx, ak), if matches!(&**e, Expr::Lam(..));

      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         state_e(e, ctx, ak),
         if let Expr::Var(x) = &**e,
         stored_val(SAddrV { x: x.clone(), ctx: ctx.clone() }, v);

      // A-IfT / A-IfF
      state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(Arc::from("#t")), et.clone()) <--
         state_a(v, ak), if sif_true(v),
         stored_kont(ak, ?SKont::If { true_branch: et, ctx: ctx_k, next_ak, .. });

      state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(Arc::from("#f")), ef.clone()) <--
         state_a(?SValue::Bool(b), ak), if b.as_ref() == "#f",
         stored_kont(ak, ?SKont::If { false_branch: ef, ctx: ctx_k, next_ak, .. });

      // A-C/cc (closure applied to captured continuation)
      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(SAddrV { x: x.clone(), ctx: ectx.clone() }, SValue::Kont(ak.clone())),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(SValue::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
         state_a(?SValue::Closure { e: elam, ctx: ctx_clo }, ak),
         stored_kont(ak, ?SKont::Callcc { ectx, next_ak }),
         if let Expr::Lam(params, ebody) = &**elam,
         if !params.is_empty(),
         let x = params[0].clone();

      // A-C/ccKont
      state_a(SValue::Kont(ak.clone()), bk.clone()),
      flow_aa(SValue::Kont(bk.clone()), SValue::Kont(ak.clone())) <--
         state_a(?SValue::Kont(bk), ak),
         stored_kont(ak, ?SKont::Callcc { .. });

      // A-Ar
      state_e(earg.clone(), ctx.clone(), SAddrK { e: earg.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: earg.clone(), ctx: ctx.clone() },
                  SKont::Fn { func: v.clone(), pos: pos as i64, ctx: ectx.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Arg { args, ctx, ectx, next_ak }),
         for (pos, earg) in args.iter().enumerate();

      // A-Call (closure)
      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(SAddrV { x: x.clone(), ctx: ectx.clone() }, v.clone()),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Fn { func: SValue::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
         if let Expr::Lam(params, ebody) = &**elam,
         if (*pos as usize) < params.len(),
         let x = params[*pos as usize].clone();

      // A-Call (captured continuation as operator)
      state_a(v.clone(), callcc_kont.clone()),
      flow_aa(v.clone(), v.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Fn { func: SValue::Kont(callcc_kont), pos: 0, .. });

      // A-Let
      state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
      stored_val(av.clone(), v.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Let { av, ebody, ctx, next_ak });

      // A-Prim1
      state_e(earg1.clone(), ctx.clone(), SAddrK { e: earg1.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: earg1.clone(), ctx: ctx.clone() },
                  SKont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg1.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Prim1 { op, e2: earg1, ctx, next_ak });

      // A-Prim2
      state_a(SValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
      flow_aa(v2.clone(), SValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
         state_a(v2, ak),
         stored_kont(ak, ?SKont::Prim2 { op, v1, next_ak });

      // A-Set!
      state_a(SValue::Number(-42), next_ak.clone()),
      stored_val(loc.clone(), v.clone()),
      flow_aa(v.clone(), SValue::Number(-42)) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Set { loc, next_ak });
   };

   StructuredStats {
      m,
      state_e: prog.state_e.len(),
      state_a: prog.state_a.len(),
      stored_val: prog.stored_val.len(),
      stored_kont: prog.stored_kont.len(),
      flow_ee: prog.flow_ee.len(),
      flow_ea: prog.flow_ea.len(),
      flow_ae: prog.flow_ae.len(),
      flow_aa: prog.flow_aa.len(),
      peek_ctx: prog.peek_ctx.len(),
      copy_ctx: prog.copy_ctx.len(),
   }
}
