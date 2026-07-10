//! # `m`-CFA for Scheme, in Ascent
//!
//! A reproduction of the analysis from
//!
//! > Davis Ross Silverman, Yihao Sun, Kristopher Micinski, Thomas Gilray.
//! > *So You Want To Analyze Scheme Programs With Datalog?* Scheme and
//! > Functional Programming Workshop, 2021.
//!
//! The paper implements a control-flow analysis (`m`-CFA, via the *Abstracting
//! Abstract Machines* methodology) for a significant subset of Scheme in the
//! Soufflé Datalog engine. This crate ports the full implementation from the
//! paper's Appendix A to [Ascent](https://github.com/s-arash/ascent),
//! Datalog-in-Rust.
//!
//! The port follows the Soufflé program closely: the Soufflé algebraic data
//! types (`value`, `kont`, `context`, `address_k`, `address_v`) become Rust
//! enums/structs, and every Soufflé rule maps to an Ascent rule (see the
//! `ascent!` block below, whose comments name the corresponding
//! Appendix-A/operational-semantics rule).
//!
//! Following the appendix, the context is a **single** expression id
//! (`Context{ctx0:id}`), i.e. the concrete instance the paper's code
//! implements. `m`-CFA with a length-`m` contour is obtained by generalizing
//! this to a bounded list; see `README.md`.

// Ascent generates internal index accumulators (e.g. `if__indices_0_total`)
// whose names are derived from the relation names; silence the resulting
// snake-case lint noise for `if_`/`let_`.
#![allow(non_snake_case)]

use std::sync::{Arc, LazyLock};

use ascent::ascent;

pub mod aam;
pub mod aam_delta;
pub mod ast;
pub mod edb;
pub mod freevar;
pub mod generic;
pub mod hybrid;
pub mod parallel;
pub mod structured;
pub mod structured_tuned;
pub mod tuned;

pub use aam::{AamStats, analyze_aam};
pub use aam_delta::analyze_aam_delta;
pub use ast::{Ast, Sym, church_term, feature_term, worst_case_term, worst_case_term_single};
pub use edb::Facts;
pub use freevar::freevars;
pub use generic::{GenericStats, analyze_generic};
pub use hybrid::{analyze_structured_hybrid, analyze_structured_hybrid_memo};
pub use parallel::analyze_generic_par;
pub use structured::{StructuredStats, analyze_structured, analyze_structured_run, to_expr, to_expr_labeled};
pub use structured_tuned::analyze_structured_tuned;
pub use tuned::McfaTuned;

/// `context = Context{ctx0:id}` — a length-1 contour of expression ids.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Ctx(pub Sym);

/// `address_k = KAddress{e:id, ctx:context}` — continuation address.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AddrK {
   pub e: Sym,
   pub ctx: Ctx,
}

/// `address_v = VAddress{x:symbol, ctx:context}` — value address.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AddrV {
   pub x: Sym,
   pub ctx: Ctx,
}

/// `value = Number | Bool | Kont | Closure | PrimVal`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
   Number(i64),
   Bool(Sym),
   Kont(AddrK),
   Closure { e: Sym, ctx: Ctx },
   PrimVal { op: Sym, v1: Box<Value>, v2: Box<Value> },
}

/// `kont = MT | Arg | Fn | Set | If | Callcc | Let | Prim1 | Prim2`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Kont {
   MT,
   Arg { args: Sym, ctx: Ctx, ectx: Ctx, next_ak: AddrK },
   Fn { func: Value, pos: i64, ctx: Ctx, next_ak: AddrK },
   Set { loc: AddrV, next_ak: AddrK },
   If { true_branch: Sym, false_branch: Sym, ctx: Ctx, next_ak: AddrK },
   Callcc { ectx: Ctx, next_ak: AddrK },
   Let { av: AddrV, ebody: Sym, ctx: Ctx, next_ak: AddrK },
   Prim1 { op: Sym, e2: Sym, ctx: Ctx, next_ak: AddrK },
   Prim2 { op: Sym, v1: Value, next_ak: AddrK },
}

static MT: LazyLock<Sym> = LazyLock::new(|| Arc::from(""));
static TT: LazyLock<Sym> = LazyLock::new(|| Arc::from("#t"));
static FF: LazyLock<Sym> = LazyLock::new(|| Arc::from("#f"));

/// The empty context `$Context("")`.
pub(crate) fn mt() -> Sym { MT.clone() }
/// The `#t` symbol.
pub(crate) fn tt() -> Sym { TT.clone() }
/// The `#f` symbol.
pub(crate) fn ff() -> Sym { FF.clone() }

/// The set of values the appendix treats as "true" in the A-IfT rule: any
/// value except `#f` (and except `PrimVal`, which — faithfully to the paper —
/// the appendix's A-If rules do not handle).
pub(crate) fn if_true(v: &Value) -> bool {
   matches!(v, Value::Closure { .. } | Value::Number(_) | Value::Kont(_))
      || matches!(v, Value::Bool(b) if b.as_ref() == "#t")
}

ascent! {
   pub struct Mcfa;

   // ===================== Input (EDB) relations =====================
   // These mirror the `.input` relations declared in Appendix A.
   relation top_exp(Sym);
   relation lambda(Sym, Sym, Sym);          // Id, Vars, BodyId
   relation lambda_arg_list(Sym, i64, Sym); // Vars, Pos, X
   relation prim(Sym, Sym);                 // Id, OpName (unused by the rules)
   relation prim_call(Sym, Sym, Sym);       // Id, PrimId, Args
   relation call(Sym, Sym, Sym);            // Id, FuncId, Args
   relation call_arg_list(Sym, i64, Sym);   // Args, Pos, X
   relation var(Sym, Sym);                  // Id, MetaName
   relation num(Sym, i64);                  // Id, v
   relation boolean(Sym, Sym);              // Id, v   (Soufflé `bool`)
   relation quotation(Sym, Sym);            // Id, Expr (unused)
   relation if_(Sym, Sym, Sym, Sym);        // Id, Guard, True, False
   relation setb(Sym, Sym, Sym);            // Id, Var, Expr
   relation callcc(Sym, Sym);               // Id, Expr
   relation let_(Sym, Sym, Sym);            // Id, BindList, Body
   relation let_list(Sym, Sym, Sym);        // BindList, X, EId

   // ===================== Derived relations =====================
   relation value_form(Sym);
   relation freevar(Sym, Sym);              // x (name), e (expr id)
   relation state_e(Sym, Ctx, AddrK);       // Eval state:  ⟨e, ctx, aκ⟩
   relation state_a(Value, AddrK);          // Apply state: ⟨v, aκ⟩
   relation stored_val(AddrV, Value);       // value store  σ̂ᵥ
   relation stored_kont(AddrK, Kont);       // kont  store  σ̂κ
   relation flow_ee(Sym, Sym);              // flow graph edges (the "results")
   relation flow_ea(Sym, Value);
   relation flow_aa(Value, Value);
   relation flow_ae(Value, Sym);
   relation peek_ctx(Sym, Ctx, Ctx);        // new-context helper (≈ new-hat)
   relation copy_ctx(Ctx, Ctx, Sym);        // signal a flat-closure env copy

   // ----- value_form -----
   value_form(id.clone()) <--
      (num(id, _) | var(id, _) | lambda(id, _, _) | quotation(id, _) | boolean(id, _));

   // ----- freevar -----
   freevar(x.clone(), e.clone()) <-- var(e, x);
   freevar(x.clone(), e.clone()) <--
      lambda(e, vars, body), freevar(x, body), !lambda_arg_list(vars, _, x);
   freevar(x.clone(), e.clone()) <--
      call(e, func, args), (freevar(x, func) | freevar(x, args));
   freevar(x.clone(), e.clone()) <--
      prim_call(e, _, args), freevar(x, args);
   freevar(x.clone(), e.clone()) <--
      call_arg_list(e, _, arg), freevar(x, arg);
   freevar(x.clone(), e.clone()) <--
      if_(e, eguard, et, ef), (freevar(x, eguard) | freevar(x, et) | freevar(x, ef));
   freevar(y.clone(), e.clone()) <--
      setb(e, _, ev), freevar(y, ev);
   freevar(x.clone(), e.clone()) <--
      callcc(e, ev), freevar(x, ev);
   freevar(x.clone(), e.clone()) <--
      let_(e, binds, body), (freevar(x, binds) | freevar(x, body));
   freevar(x.clone(), e.clone()) <--
      let_list(e, _, bind), freevar(x, bind), !let_list(e, x, _);

   // ----- injection of the top expression (Iˆ) -----
   state_e(e.clone(), Ctx(mt()), AddrK { e: e.clone(), ctx: Ctx(mt()) }),
   peek_ctx(e.clone(), Ctx(mt()), Ctx(e.clone())),
   stored_kont(AddrK { e: e.clone(), ctx: Ctx(mt()) }, Kont::MT) <--
      top_exp(e);

   // ----- peek_ctx: compute the "new" context on demand (≈ new-hat) -----
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <--
      state_e(e, old, _),
      (callcc(e, _) | call(e, _, _) | let_(e, _, _) | lambda(e, _, _));

   // ----- copy_ctx: copy free-variable bindings between contexts (≈ copy-hat) -----
   stored_val(AddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
      copy_ctx(from, to, e),
      freevar(fv, e),
      stored_val(AddrV { x: fv.clone(), ctx: from.clone() }, v);

   // ----- E-If -----
   state_e(eguard.clone(), ctx.clone(), AddrK { e: eguard.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: eguard.clone(), ctx: ctx.clone() },
               Kont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), eguard.clone()) <--
      state_e(e, ctx, ak),
      if_(e, eguard, et, ef);

   // ----- E-C/cc -----
   state_e(elam.clone(), ctx.clone(), AddrK { e: elam.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: elam.clone(), ctx: ctx.clone() },
               Kont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), elam.clone()) <--
      state_e(e, ctx, ak),
      callcc(e, elam),
      peek_ctx(e, ctx, ectx);

   // ----- E-Set! -----
   state_e(esetto.clone(), ctx.clone(), AddrK { e: esetto.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: esetto.clone(), ctx: ctx.clone() },
               Kont::Set { loc: AddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
   flow_ee(e.clone(), esetto.clone()) <--
      state_e(e, ctx, ak),
      setb(e, x, esetto);

   // ----- E-Call -----
   state_e(efunc.clone(), ctx.clone(), AddrK { e: efunc.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: efunc.clone(), ctx: ctx.clone() },
               Kont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), efunc.clone()) <--
      state_e(e, ctx, ak),
      call(e, efunc, eargs),
      peek_ctx(e, ctx, ectx);

   // ----- E-Let -----
   state_e(ebnd.clone(), ctx.clone(), AddrK { e: ebnd.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: ebnd.clone(), ctx: ctx.clone() },
               Kont::Let { av: AddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
   copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
   flow_ee(e.clone(), ebnd.clone()) <--
      state_e(e, ctx, ak),
      let_(e, ll, ebody),
      let_list(ll, x, ebnd),
      peek_ctx(e, ctx, ectx);

   // ----- E-Prim -----
   state_e(earg0.clone(), ctx.clone(), AddrK { e: earg0.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg0.clone(), ctx: ctx.clone() },
               Kont::Prim1 { op: op.clone(), e2: earg1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), earg0.clone()) <--
      state_e(e, ctx, ak),
      prim_call(e, op, pl),
      call_arg_list(pl, p0, earg0), if *p0 == 0,
      call_arg_list(pl, p1, earg1), if *p1 == 1;

   // ----- Atomic evaluation (E-AE): num / bool / lambda / var -----
   state_a(Value::Number(*n), ak.clone()),
   flow_ea(e.clone(), Value::Number(*n)) <--
      state_e(e, _, ak),
      num(e, n);

   state_a(Value::Bool(b.clone()), ak.clone()),
   flow_ea(e.clone(), Value::Bool(b.clone())) <--
      state_e(e, _, ak),
      boolean(e, b);

   state_a(Value::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
   flow_ea(e.clone(), Value::Closure { e: e.clone(), ctx: ctx.clone() }) <--
      state_e(e, ctx, ak),
      lambda(e, _, _);

   state_a(v.clone(), ak.clone()),
   flow_ea(e.clone(), v.clone()) <--
      state_e(e, ctx, ak),
      var(e, x),
      stored_val(AddrV { x: x.clone(), ctx: ctx.clone() }, v);

   // ----- A-IfT: any non-#f value takes the true branch -----
   state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(tt()), et.clone()) <--
      state_a(v, ak),
      if if_true(v),
      stored_kont(ak, ?Kont::If { true_branch: et, ctx: ctx_k, next_ak, .. });

   // ----- A-IfF: #f takes the false branch -----
   state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(ff()), ef.clone()) <--
      state_a(?Value::Bool(b), ak), if b.as_ref() == "#f",
      stored_kont(ak, ?Kont::If { false_branch: ef, ctx: ctx_k, next_ak, .. });

   // ----- A-C/cc: apply a closure to the captured continuation -----
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, Value::Kont(ak.clone())),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(Value::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
      state_a(?Value::Closure { e: elam, ctx: ctx_clo }, ak),
      stored_kont(ak, ?Kont::Callcc { ectx, next_ak }),
      lambda(elam, params, ebody),
      lambda_arg_list(params, p0, x), if *p0 == 0;

   // ----- A-C/ccKont: a continuation applied under call/cc -----
   state_a(Value::Kont(ak.clone()), bk.clone()),
   flow_aa(Value::Kont(bk.clone()), Value::Kont(ak.clone())) <--
      state_a(?Value::Kont(bk), ak),
      stored_kont(ak, ?Kont::Callcc { .. });

   // ----- A-Ar: evaluate an argument, remembering the function via Fn -----
   state_e(earg.clone(), ctx.clone(), AddrK { e: earg.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg.clone(), ctx: ctx.clone() },
               Kont::Fn { func: v.clone(), pos: *pos, ctx: ectx.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Arg { args: eargs, ctx, ectx, next_ak }),
      call_arg_list(eargs, pos, earg);

   // ----- A-Call: apply a closure, binding the parameter at position `pos` -----
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, v.clone()),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
      lambda(elam, params, ebody),
      lambda_arg_list(params, pos, x);

   // ----- A-Call (continuation as operator): jump to the captured continuation -----
   state_a(v.clone(), callcc_kont.clone()),
   flow_aa(v.clone(), v.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Kont(callcc_kont), pos: 0, .. });

   // ----- A-Let: bind the let variable and evaluate the body -----
   state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
   stored_val(av.clone(), v.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Let { av, ebody, ctx, next_ak });

   // ----- A-Prim1: first operand evaluated, evaluate the second -----
   state_e(earg1.clone(), ctx.clone(), AddrK { e: earg1.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg1.clone(), ctx: ctx.clone() },
               Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg1.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Prim1 { op, e2: earg1, ctx, next_ak });

   // ----- A-Prim2: both operands evaluated, produce the primitive value -----
   state_a(Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
   flow_aa(v2.clone(), Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
      state_a(v2, ak),
      stored_kont(ak, ?Kont::Prim2 { op, v1, next_ak });

   // ----- A-Set!: perform the mutation, produce the sentinel -42 -----
   state_a(Value::Number(-42), next_ak.clone()),
   stored_val(loc.clone(), v.clone()),
   flow_aa(v.clone(), Value::Number(-42)) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Set { loc, next_ak });
}

impl Facts {
   /// Load these input facts into a fresh, un-run [`Mcfa`] program.
   pub fn into_program(self) -> Mcfa {
      let mut p = Mcfa::default();
      p.top_exp = self.top_exp;
      p.lambda = self.lambda;
      p.lambda_arg_list = self.lambda_arg_list;
      p.prim = self.prim;
      p.prim_call = self.prim_call;
      p.call = self.call;
      p.call_arg_list = self.call_arg_list;
      p.var = self.var;
      p.num = self.num;
      p.boolean = self.boolean;
      p.quotation = self.quotation;
      p.if_ = self.if_;
      p.setb = self.setb;
      p.callcc = self.callcc;
      p.let_ = self.let_;
      p.let_list = self.let_list;
      p
   }
}

/// Convenience: build, load, and run the analysis on an AST.
pub fn analyze(ast: &Ast) -> Mcfa {
   let mut prog = Facts::from_ast(ast).into_program();
   prog.run();
   prog
}
