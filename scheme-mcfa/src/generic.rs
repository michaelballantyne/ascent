//! **Variation: tunable polyvariance `m` (0/1/2/...-CFA).**
//!
//! The paper's Appendix A hard-codes `context = Context{ctx0:id}`, i.e. a
//! length-1 contour (`m=1`). To reproduce the paper's headline experiment —
//! sweeping `m ∈ {0,1,2}` (Table 1) — this module generalizes the context to a
//! bounded list of the most-recent `m` binding-site expressions.
//!
//! Every rule is identical to the faithful port in [`crate`]; the *only*
//! semantic change is how a new context is formed:
//!
//! * empty context is now the empty list `[]` (rather than `Context("")`), and
//! * `peek_ctx` extends the contour with [`extend_ctx`] instead of always
//!   replacing it with the current expression.
//!
//! Because `m` is a runtime value we use [`ascent::ascent_run`] (which captures
//! local variables) rather than the `ascent!` item macro.

use std::sync::Arc;

use ascent::ascent_run;

use crate::Facts;
use crate::ast::Sym;

/// `context` — the most-recent (up to) `m` binding-site expression ids, newest
/// first.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GCtx(pub Vec<Sym>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GAddrK { pub e: Sym, pub ctx: GCtx }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GAddrV { pub x: Sym, pub ctx: GCtx }

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum GValue {
   Number(i64),
   Bool(Sym),
   Kont(GAddrK),
   Closure { e: Sym, ctx: GCtx },
   PrimVal { op: Sym, v1: Box<GValue>, v2: Box<GValue> },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum GKont {
   MT,
   Arg { args: Sym, ctx: GCtx, ectx: GCtx, next_ak: GAddrK },
   Fn { func: GValue, pos: i64, ctx: GCtx, next_ak: GAddrK },
   Set { loc: GAddrV, next_ak: GAddrK },
   If { true_branch: Sym, false_branch: Sym, ctx: GCtx, next_ak: GAddrK },
   Callcc { ectx: GCtx, next_ak: GAddrK },
   Let { av: GAddrV, ebody: Sym, ctx: GCtx, next_ak: GAddrK },
   Prim1 { op: Sym, e2: Sym, ctx: GCtx, next_ak: GAddrK },
   Prim2 { op: Sym, v1: GValue, next_ak: GAddrK },
}

/// `new`/`⌊·⌋ₘ`: push binding site `e` onto the contour, keeping only the
/// newest `m` entries. `m=0` yields the (context-insensitive) empty contour.
fn extend_ctx(e: &Sym, old: &GCtx, m: usize) -> GCtx {
   if m == 0 {
      return GCtx(Vec::new());
   }
   let mut v = Vec::with_capacity(m);
   v.push(e.clone());
   v.extend(old.0.iter().take(m - 1).cloned());
   GCtx(v)
}

fn gif_true(v: &GValue) -> bool {
   matches!(v, GValue::Closure { .. } | GValue::Number(_) | GValue::Kont(_))
      || matches!(v, GValue::Bool(b) if b.as_ref() == "#t")
}

/// Result of a generic `m`-CFA run: the sizes of every relation.
#[derive(Clone, Debug, Default)]
pub struct GenericStats {
   pub m: usize,
   pub state_e: usize,
   pub state_a: usize,
   pub stored_val: usize,
   pub stored_kont: usize,
   pub flow_ee: usize,
   pub flow_ea: usize,
   pub flow_ae: usize,
   pub flow_aa: usize,
   pub freevar: usize,
   pub peek_ctx: usize,
   pub copy_ctx: usize,
   /// `flow_ee` edges, for cross-checking against the faithful `m=1` port.
   pub flow_ee_edges: Vec<(Sym, Sym)>,
}

impl GenericStats {
   pub fn total_derived(&self) -> usize {
      self.state_e + self.state_a + self.stored_val + self.stored_kont
         + self.flow_ee + self.flow_ea + self.flow_ae + self.flow_aa
   }
}

/// Run `m`-CFA on `facts` for an arbitrary polyvariance `m`.
pub fn analyze_generic(facts: &Facts, m: usize) -> GenericStats {
   let empty = GCtx(Vec::new());

   let prog = ascent_run! {
      relation top_exp(Sym) = facts.top_exp.clone();
      relation lambda(Sym, Sym, Sym) = facts.lambda.clone();
      relation lambda_arg_list(Sym, i64, Sym) = facts.lambda_arg_list.clone();
      relation prim(Sym, Sym) = facts.prim.clone();
      relation prim_call(Sym, Sym, Sym) = facts.prim_call.clone();
      relation call(Sym, Sym, Sym) = facts.call.clone();
      relation call_arg_list(Sym, i64, Sym) = facts.call_arg_list.clone();
      relation var(Sym, Sym) = facts.var.clone();
      relation num(Sym, i64) = facts.num.clone();
      relation boolean(Sym, Sym) = facts.boolean.clone();
      relation quotation(Sym, Sym) = facts.quotation.clone();
      relation if_(Sym, Sym, Sym, Sym) = facts.if_.clone();
      relation setb(Sym, Sym, Sym) = facts.setb.clone();
      relation callcc(Sym, Sym) = facts.callcc.clone();
      relation let_(Sym, Sym, Sym) = facts.let_.clone();
      relation let_list(Sym, Sym, Sym) = facts.let_list.clone();

      relation value_form(Sym);
      relation freevar(Sym, Sym);
      relation state_e(Sym, GCtx, GAddrK);
      relation state_a(GValue, GAddrK);
      relation stored_val(GAddrV, GValue);
      relation stored_kont(GAddrK, GKont);
      relation flow_ee(Sym, Sym);
      relation flow_ea(Sym, GValue);
      relation flow_aa(GValue, GValue);
      relation flow_ae(GValue, Sym);
      relation peek_ctx(Sym, GCtx, GCtx);
      relation copy_ctx(GCtx, GCtx, Sym);

      value_form(id.clone()) <--
         (num(id, _) | var(id, _) | lambda(id, _, _) | quotation(id, _) | boolean(id, _));

      freevar(x.clone(), e.clone()) <-- var(e, x);
      freevar(x.clone(), e.clone()) <--
         lambda(e, vars, body), freevar(x, body), !lambda_arg_list(vars, _, x);
      freevar(x.clone(), e.clone()) <--
         call(e, func, args), (freevar(x, func) | freevar(x, args));
      freevar(x.clone(), e.clone()) <-- prim_call(e, _, args), freevar(x, args);
      freevar(x.clone(), e.clone()) <-- call_arg_list(e, _, arg), freevar(x, arg);
      freevar(x.clone(), e.clone()) <--
         if_(e, eguard, et, ef), (freevar(x, eguard) | freevar(x, et) | freevar(x, ef));
      freevar(y.clone(), e.clone()) <-- setb(e, _, ev), freevar(y, ev);
      freevar(x.clone(), e.clone()) <-- callcc(e, ev), freevar(x, ev);
      freevar(x.clone(), e.clone()) <--
         let_(e, binds, body), (freevar(x, binds) | freevar(x, body));
      freevar(x.clone(), e.clone()) <--
         let_list(e, _, bind), freevar(x, bind), !let_list(e, x, _);

      // injection: empty contour []
      state_e(e.clone(), empty.clone(), GAddrK { e: e.clone(), ctx: empty.clone() }),
      peek_ctx(e.clone(), empty.clone(), extend_ctx(e, &empty, m)),
      stored_kont(GAddrK { e: e.clone(), ctx: empty.clone() }, GKont::MT) <--
         top_exp(e);

      // peek_ctx: extend the contour by the current binding site (length-m)
      peek_ctx(e.clone(), old.clone(), extend_ctx(e, old, m)) <--
         state_e(e, old, _),
         (callcc(e, _) | call(e, _, _) | let_(e, _, _) | lambda(e, _, _));

      stored_val(GAddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
         copy_ctx(from, to, e),
         freevar(fv, e),
         stored_val(GAddrV { x: fv.clone(), ctx: from.clone() }, v);

      state_e(eguard.clone(), ctx.clone(), GAddrK { e: eguard.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: eguard.clone(), ctx: ctx.clone() },
                  GKont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), eguard.clone()) <--
         state_e(e, ctx, ak), if_(e, eguard, et, ef);

      state_e(elam.clone(), ctx.clone(), GAddrK { e: elam.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: elam.clone(), ctx: ctx.clone() },
                  GKont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), elam.clone()) <--
         state_e(e, ctx, ak), callcc(e, elam), peek_ctx(e, ctx, ectx);

      state_e(esetto.clone(), ctx.clone(), GAddrK { e: esetto.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: esetto.clone(), ctx: ctx.clone() },
                  GKont::Set { loc: GAddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
      flow_ee(e.clone(), esetto.clone()) <--
         state_e(e, ctx, ak), setb(e, x, esetto);

      state_e(efunc.clone(), ctx.clone(), GAddrK { e: efunc.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: efunc.clone(), ctx: ctx.clone() },
                  GKont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), efunc.clone()) <--
         state_e(e, ctx, ak), call(e, efunc, eargs), peek_ctx(e, ctx, ectx);

      state_e(ebnd.clone(), ctx.clone(), GAddrK { e: ebnd.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: ebnd.clone(), ctx: ctx.clone() },
                  GKont::Let { av: GAddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
      copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
      flow_ee(e.clone(), ebnd.clone()) <--
         state_e(e, ctx, ak), let_(e, ll, ebody), let_list(ll, x, ebnd), peek_ctx(e, ctx, ectx);

      state_e(earg0.clone(), ctx.clone(), GAddrK { e: earg0.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: earg0.clone(), ctx: ctx.clone() },
                  GKont::Prim1 { op: op.clone(), e2: earg1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), earg0.clone()) <--
         state_e(e, ctx, ak),
         prim_call(e, op, pl),
         call_arg_list(pl, p0, earg0), if *p0 == 0,
         call_arg_list(pl, p1, earg1), if *p1 == 1;

      state_a(GValue::Number(*n), ak.clone()),
      flow_ea(e.clone(), GValue::Number(*n)) <-- state_e(e, _, ak), num(e, n);

      state_a(GValue::Bool(b.clone()), ak.clone()),
      flow_ea(e.clone(), GValue::Bool(b.clone())) <-- state_e(e, _, ak), boolean(e, b);

      state_a(GValue::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
      flow_ea(e.clone(), GValue::Closure { e: e.clone(), ctx: ctx.clone() }) <--
         state_e(e, ctx, ak), lambda(e, _, _);

      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         state_e(e, ctx, ak), var(e, x), stored_val(GAddrV { x: x.clone(), ctx: ctx.clone() }, v);

      state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(GValue::Bool(Arc::from("#t")), et.clone()) <--
         state_a(v, ak), if gif_true(v),
         stored_kont(ak, ?GKont::If { true_branch: et, ctx: ctx_k, next_ak, .. });

      state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(GValue::Bool(Arc::from("#f")), ef.clone()) <--
         state_a(?GValue::Bool(b), ak), if b.as_ref() == "#f",
         stored_kont(ak, ?GKont::If { false_branch: ef, ctx: ctx_k, next_ak, .. });

      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(GAddrV { x: x.clone(), ctx: ectx.clone() }, GValue::Kont(ak.clone())),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(GValue::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
         state_a(?GValue::Closure { e: elam, ctx: ctx_clo }, ak),
         stored_kont(ak, ?GKont::Callcc { ectx, next_ak }),
         lambda(elam, params, ebody),
         lambda_arg_list(params, p0, x), if *p0 == 0;

      state_a(GValue::Kont(ak.clone()), bk.clone()),
      flow_aa(GValue::Kont(bk.clone()), GValue::Kont(ak.clone())) <--
         state_a(?GValue::Kont(bk), ak),
         stored_kont(ak, ?GKont::Callcc { .. });

      state_e(earg.clone(), ctx.clone(), GAddrK { e: earg.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: earg.clone(), ctx: ctx.clone() },
                  GKont::Fn { func: v.clone(), pos: *pos, ctx: ectx.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Arg { args: eargs, ctx, ectx, next_ak }),
         call_arg_list(eargs, pos, earg);

      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(GAddrV { x: x.clone(), ctx: ectx.clone() }, v.clone()),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Fn { func: GValue::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
         lambda(elam, params, ebody),
         lambda_arg_list(params, pos, x);

      state_a(v.clone(), callcc_kont.clone()),
      flow_aa(v.clone(), v.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Fn { func: GValue::Kont(callcc_kont), pos: 0, .. });

      state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
      stored_val(av.clone(), v.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Let { av, ebody, ctx, next_ak });

      state_e(earg1.clone(), ctx.clone(), GAddrK { e: earg1.clone(), ctx: ctx.clone() }),
      stored_kont(GAddrK { e: earg1.clone(), ctx: ctx.clone() },
                  GKont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg1.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Prim1 { op, e2: earg1, ctx, next_ak });

      state_a(GValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
      flow_aa(v2.clone(), GValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
         state_a(v2, ak),
         stored_kont(ak, ?GKont::Prim2 { op, v1, next_ak });

      state_a(GValue::Number(-42), next_ak.clone()),
      stored_val(loc.clone(), v.clone()),
      flow_aa(v.clone(), GValue::Number(-42)) <--
         state_a(v, ak),
         stored_kont(ak, ?GKont::Set { loc, next_ak });
   };

   GenericStats {
      m,
      state_e: prog.state_e.len(),
      state_a: prog.state_a.len(),
      stored_val: prog.stored_val.len(),
      stored_kont: prog.stored_kont.len(),
      flow_ee: prog.flow_ee.len(),
      flow_ea: prog.flow_ea.len(),
      flow_ae: prog.flow_ae.len(),
      flow_aa: prog.flow_aa.len(),
      freevar: prog.freevar.len(),
      peek_ctx: prog.peek_ctx.len(),
      copy_ctx: prog.copy_ctx.len(),
      flow_ee_edges: prog.flow_ee,
   }
}
