//! A traditional Abstracting-Abstract-Machines (AAM) implementation of the
//! exact same `m`-CFA analysis — **no Datalog**, just a worklist and a global
//! store, in plain Rust.
//!
//! This is the classic store-widened CESK* fixpoint (paper, Fig. 8): states
//! carry only an expression/value and a continuation address; the value store
//! `σ̂ᵥ` and continuation store `σ̂κ` are single, global, monotone maps
//! (`VAddr → P(Value)`, `KAddr → P(Kont)`). The worklist is event-driven and
//! semi-naive: each derived fact (a new state, a new store binding, a new
//! copy-edge) is processed exactly once, and store growth re-fires only the
//! states that read the changed address.
//!
//! It deliberately reuses the *same* value/kont/context types as
//! [`crate::generic`], and evaluates over the same flat [`Facts`], so its
//! output is directly comparable to the Datalog analyses — indeed
//! `tests/aam_check.rs` asserts it computes bit-for-bit the same relations as
//! [`crate::analyze_generic`].

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

use crate::Facts;
use crate::ast::Sym;
use crate::generic::{GAddrK, GAddrV, GCtx, GKont, GValue, extend_ctx, gif_true};

/// A syntax node, indexed by expression id (mirrors the flat relations).
#[derive(Clone)]
enum Node {
   Var(Sym),
   Num(i64),
   Bool(Sym),
   Lam { params: Rc<Vec<Sym>>, body: Sym },
   App { func: Sym, args_id: Sym },
   If(Sym, Sym, Sym),
   Let { binds: Rc<Vec<(Sym, Sym)>>, body: Sym },
   Set(Sym, Sym),
   Callcc(Sym),
   Prim { op: Sym, e0: Sym, e1: Sym },
}

/// The program: the labelled AST plus precomputed free variables.
struct Program {
   node: HashMap<Sym, Node>,
   call_args: HashMap<Sym, Vec<Sym>>, // arg-list id -> ordered argument ids
   freevars: HashMap<Sym, Rc<HashSet<Sym>>>,
   top: Sym,
}

impl Program {
   fn from_facts(facts: &Facts) -> Program {
      // arg-list id -> [arg ids] (ordered by position); shared by calls and prims
      let mut call_args: HashMap<Sym, Vec<(i64, Sym)>> = HashMap::new();
      for (aid, pos, x) in &facts.call_arg_list {
         call_args.entry(aid.clone()).or_default().push((*pos, x.clone()));
      }
      let call_args: HashMap<Sym, Vec<Sym>> = call_args
         .into_iter()
         .map(|(k, mut v)| {
            v.sort_by_key(|(p, _)| *p);
            (k, v.into_iter().map(|(_, x)| x).collect())
         })
         .collect();

      // param-list id -> [param names] (ordered)
      let mut lam_args: HashMap<Sym, Vec<(i64, Sym)>> = HashMap::new();
      for (pid, pos, x) in &facts.lambda_arg_list {
         lam_args.entry(pid.clone()).or_default().push((*pos, x.clone()));
      }
      let lam_params: HashMap<Sym, Rc<Vec<Sym>>> = lam_args
         .into_iter()
         .map(|(k, mut v)| {
            v.sort_by_key(|(p, _)| *p);
            (k, Rc::new(v.into_iter().map(|(_, x)| x).collect()))
         })
         .collect();

      // let-binding-list id -> [(name, expr id)]
      let mut let_binds: HashMap<Sym, Vec<(Sym, Sym)>> = HashMap::new();
      for (bl, x, e) in &facts.let_list {
         let_binds.entry(bl.clone()).or_default().push((x.clone(), e.clone()));
      }

      let mut node = HashMap::new();
      for (id, x) in &facts.var {
         node.insert(id.clone(), Node::Var(x.clone()));
      }
      for (id, n) in &facts.num {
         node.insert(id.clone(), Node::Num(*n));
      }
      for (id, b) in &facts.boolean {
         node.insert(id.clone(), Node::Bool(b.clone()));
      }
      for (id, vars, body) in &facts.lambda {
         let params = lam_params.get(vars).cloned().unwrap_or_else(|| Rc::new(Vec::new()));
         node.insert(id.clone(), Node::Lam { params, body: body.clone() });
      }
      for (id, func, args) in &facts.call {
         node.insert(id.clone(), Node::App { func: func.clone(), args_id: args.clone() });
      }
      for (id, g, t, f) in &facts.if_ {
         node.insert(id.clone(), Node::If(g.clone(), t.clone(), f.clone()));
      }
      for (id, bl, body) in &facts.let_ {
         let binds = Rc::new(let_binds.get(bl).cloned().unwrap_or_default());
         node.insert(id.clone(), Node::Let { binds, body: body.clone() });
      }
      for (id, x, e) in &facts.setb {
         node.insert(id.clone(), Node::Set(x.clone(), e.clone()));
      }
      for (id, e) in &facts.callcc {
         node.insert(id.clone(), Node::Callcc(e.clone()));
      }
      for (id, op, args) in &facts.prim_call {
         let a = &call_args[args];
         node.insert(id.clone(), Node::Prim { op: op.clone(), e0: a[0].clone(), e1: a[1].clone() });
      }

      let top = facts.top_exp[0].0.clone();
      let mut prog =
         Program { node, call_args, freevars: HashMap::new(), top };
      // Precompute free variables (matching the paper's `freevar` relation).
      let ids: Vec<Sym> = prog.node.keys().cloned().collect();
      for id in ids {
         prog.free_vars(&id);
      }
      prog
   }

   /// Free variables of `e`, memoized. Matches Appendix A's `freevar`: `set!`'s
   /// target is not counted free, and a `let` body is not scoped by the
   /// let-bound names.
   fn free_vars(&mut self, e: &Sym) -> Rc<HashSet<Sym>> {
      if let Some(fv) = self.freevars.get(e) {
         return fv.clone();
      }
      let node = self.node[e].clone();
      let mut s: HashSet<Sym> = HashSet::new();
      match node {
         Node::Var(x) => {
            s.insert(x);
         }
         Node::Num(_) | Node::Bool(_) => {}
         Node::Lam { params, body } => {
            for v in self.free_vars(&body).iter() {
               if !params.contains(v) {
                  s.insert(v.clone());
               }
            }
         }
         Node::App { func, args_id } => {
            s.extend(self.free_vars(&func).iter().cloned());
            for a in self.call_args[&args_id].clone() {
               s.extend(self.free_vars(&a).iter().cloned());
            }
         }
         Node::Prim { op: _, e0, e1 } => {
            s.extend(self.free_vars(&e0).iter().cloned());
            s.extend(self.free_vars(&e1).iter().cloned());
         }
         Node::If(g, t, f) => {
            s.extend(self.free_vars(&g).iter().cloned());
            s.extend(self.free_vars(&t).iter().cloned());
            s.extend(self.free_vars(&f).iter().cloned());
         }
         Node::Set(_x, ev) => s.extend(self.free_vars(&ev).iter().cloned()),
         Node::Callcc(ev) => s.extend(self.free_vars(&ev).iter().cloned()),
         Node::Let { binds, body } => {
            let bound: HashSet<&Sym> = binds.iter().map(|(x, _)| x).collect();
            for (_, be) in binds.iter() {
               for v in self.free_vars(be).iter() {
                  if !bound.contains(v) {
                     s.insert(v.clone());
                  }
               }
            }
            s.extend(self.free_vars(&body).iter().cloned());
         }
      }
      let r = Rc::new(s);
      self.freevars.insert(e.clone(), r.clone());
      r
   }
}

/// Relation sizes from an AAM run (same shape as [`crate::GenericStats`]).
#[derive(Clone, Debug, Default)]
pub struct AamStats {
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
   pub flow_ee_edges: Vec<(Sym, Sym)>,
}

impl AamStats {
   pub fn total_derived(&self) -> usize {
      self.state_e + self.state_a + self.stored_val + self.stored_kont
         + self.flow_ee + self.flow_ea + self.flow_ae + self.flow_aa
   }
}

enum Event {
   Eval(Sym, GCtx, GAddrK),
   Apply(GValue, GAddrK),
   Kont(GAddrK, GKont),
   Val(GAddrV, GValue),
   Copy(GCtx, GCtx, Sym),
}

struct Aam<'a> {
   prog: &'a Program,
   m: usize,

   // global stores
   sv: HashMap<GAddrV, HashSet<GValue>>,
   sk: HashMap<GAddrK, HashSet<GKont>>,

   // reachable states
   evals: HashSet<(Sym, GCtx, GAddrK)>,
   applies: HashSet<(GValue, GAddrK)>,

   // derived helper relations
   copy: HashSet<(GCtx, GCtx, Sym)>,
   peek: HashSet<(Sym, GCtx, GCtx)>,

   // flow graph (the analysis "results")
   flow_ee: HashSet<(Sym, Sym)>,
   flow_ea: HashSet<(Sym, GValue)>,
   flow_ae: HashSet<(GValue, Sym)>,
   flow_aa: HashSet<(GValue, GValue)>,

   // dependency indices for store-driven re-firing
   var_reads: HashMap<GAddrV, Vec<(Sym, GAddrK)>>, // addr -> [(var-expr id, ak)]
   applies_at: HashMap<GAddrK, Vec<GValue>>,       // ak -> [applied values]
   copy_from: HashMap<GCtx, Vec<(GCtx, Sym)>>,     // from-ctx -> [(to-ctx, e)]

   wl: VecDeque<Event>,
}

fn tt() -> Sym { Arc::from("#t") }
fn ff() -> Sym { Arc::from("#f") }

impl<'a> Aam<'a> {
   fn push_eval(&mut self, e: Sym, ctx: GCtx, ak: GAddrK) {
      if self.evals.insert((e.clone(), ctx.clone(), ak.clone())) {
         self.wl.push_back(Event::Eval(e, ctx, ak));
      }
   }
   fn push_apply(&mut self, v: GValue, ak: GAddrK) {
      if self.applies.insert((v.clone(), ak.clone())) {
         self.wl.push_back(Event::Apply(v, ak));
      }
   }
   fn push_kont(&mut self, ak: GAddrK, k: GKont) {
      if self.sk.entry(ak.clone()).or_default().insert(k.clone()) {
         self.wl.push_back(Event::Kont(ak, k));
      }
   }
   fn push_val(&mut self, a: GAddrV, v: GValue) {
      if self.sv.entry(a.clone()).or_default().insert(v.clone()) {
         self.wl.push_back(Event::Val(a, v));
      }
   }
   fn push_copy(&mut self, from: GCtx, to: GCtx, e: Sym) {
      if self.copy.insert((from.clone(), to.clone(), e.clone())) {
         self.wl.push_back(Event::Copy(from, to, e));
      }
   }
   fn record_peek(&mut self, e: &Sym, ctx: &GCtx) {
      let nw = extend_ctx(e, ctx, self.m);
      self.peek.insert((e.clone(), ctx.clone(), nw));
   }

   fn run(&mut self) {
      let empty = GCtx(Vec::new());
      let top = self.prog.top.clone();
      let ak0 = GAddrK { e: top.clone(), ctx: empty.clone() };
      self.peek.insert((top.clone(), empty.clone(), extend_ctx(&top, &empty, self.m)));
      self.push_kont(ak0.clone(), GKont::MT);
      self.push_eval(top, empty, ak0);

      while let Some(ev) = self.wl.pop_front() {
         match ev {
            Event::Eval(e, ctx, ak) => self.eval(e, ctx, ak),
            Event::Apply(v, ak) => {
               self.applies_at.entry(ak.clone()).or_default().push(v.clone());
               let konts: Vec<GKont> = self.sk.get(&ak).map(|s| s.iter().cloned().collect()).unwrap_or_default();
               for k in konts {
                  self.apply(&v, &ak, &k);
               }
            }
            Event::Kont(ak, k) => {
               let vs: Vec<GValue> = self.applies_at.get(&ak).cloned().unwrap_or_default();
               for v in vs {
                  self.apply(&v, &ak, &k);
               }
            }
            Event::Val(a, v) => {
               // fire variable reads waiting on this address
               let readers: Vec<(Sym, GAddrK)> = self.var_reads.get(&a).cloned().unwrap_or_default();
               for (e, ak) in readers {
                  self.flow_ea.insert((e, v.clone()));
                  self.push_apply(v.clone(), ak);
               }
               // propagate along copy-edges out of this context
               let edges: Vec<(GCtx, Sym)> = self.copy_from.get(&a.ctx).cloned().unwrap_or_default();
               for (to, e) in edges {
                  if self.prog.freevars[&e].contains(&a.x) {
                     self.push_val(GAddrV { x: a.x.clone(), ctx: to }, v.clone());
                  }
               }
            }
            Event::Copy(from, to, e) => {
               self.copy_from.entry(from.clone()).or_default().push((to.clone(), e.clone()));
               let fvs: Vec<Sym> = self.prog.freevars[&e].iter().cloned().collect();
               for fv in fvs {
                  let src = GAddrV { x: fv.clone(), ctx: from.clone() };
                  let vals: Vec<GValue> = self.sv.get(&src).map(|s| s.iter().cloned().collect()).unwrap_or_default();
                  for v in vals {
                     self.push_val(GAddrV { x: fv.clone(), ctx: to.clone() }, v);
                  }
               }
            }
         }
      }
   }

   fn eval(&mut self, e: Sym, ctx: GCtx, ak: GAddrK) {
      match self.prog.node[&e].clone() {
         Node::Var(x) => {
            let a = GAddrV { x, ctx };
            self.var_reads.entry(a.clone()).or_default().push((e.clone(), ak.clone()));
            let vals: Vec<GValue> = self.sv.get(&a).map(|s| s.iter().cloned().collect()).unwrap_or_default();
            for v in vals {
               self.flow_ea.insert((e.clone(), v.clone()));
               self.push_apply(v, ak.clone());
            }
         }
         Node::Num(n) => {
            let v = GValue::Number(n);
            self.flow_ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         }
         Node::Bool(b) => {
            let v = GValue::Bool(b);
            self.flow_ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         }
         Node::Lam { .. } => {
            self.record_peek(&e, &ctx);
            let v = GValue::Closure { e: e.clone(), ctx: ctx.clone() };
            self.flow_ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         }
         Node::If(g, t, f) => {
            let ak2 = GAddrK { e: g.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::If { true_branch: t, false_branch: f, ctx: ctx.clone(), next_ak: ak });
            self.flow_ee.insert((e, g.clone()));
            self.push_eval(g, ctx, ak2);
         }
         Node::Callcc(elam) => {
            self.record_peek(&e, &ctx);
            let ectx = extend_ctx(&e, &ctx, self.m);
            let ak2 = GAddrK { e: elam.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::Callcc { ectx, next_ak: ak });
            self.flow_ee.insert((e, elam.clone()));
            self.push_eval(elam, ctx, ak2);
         }
         Node::Set(x, esub) => {
            let ak2 = GAddrK { e: esub.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::Set { loc: GAddrV { x, ctx: ctx.clone() }, next_ak: ak });
            self.flow_ee.insert((e, esub.clone()));
            self.push_eval(esub, ctx, ak2);
         }
         Node::App { func, args_id } => {
            self.record_peek(&e, &ctx);
            let ectx = extend_ctx(&e, &ctx, self.m);
            let ak2 = GAddrK { e: func.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::Arg { args: args_id, ctx: ctx.clone(), ectx, next_ak: ak });
            self.flow_ee.insert((e, func.clone()));
            self.push_eval(func, ctx, ak2);
         }
         Node::Let { binds, body } => {
            self.record_peek(&e, &ctx);
            let ectx = extend_ctx(&e, &ctx, self.m);
            self.push_copy(ctx.clone(), ectx.clone(), e.clone());
            for (x, ebnd) in binds.iter() {
               let ak2 = GAddrK { e: ebnd.clone(), ctx: ctx.clone() };
               self.push_kont(
                  ak2.clone(),
                  GKont::Let {
                     av: GAddrV { x: x.clone(), ctx: ectx.clone() },
                     ebody: body.clone(),
                     ctx: ectx.clone(),
                     next_ak: ak.clone(),
                  },
               );
               self.flow_ee.insert((e.clone(), ebnd.clone()));
               self.push_eval(ebnd.clone(), ctx.clone(), ak2);
            }
         }
         Node::Prim { op, e0, e1 } => {
            let ak2 = GAddrK { e: e0.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::Prim1 { op, e2: e1, ctx: ctx.clone(), next_ak: ak });
            self.flow_ee.insert((e, e0.clone()));
            self.push_eval(e0, ctx, ak2);
         }
      }
   }

   fn apply(&mut self, v: &GValue, ak: &GAddrK, k: &GKont) {
      match k {
         GKont::MT => {}
         GKont::If { true_branch, false_branch, ctx, next_ak } => {
            if gif_true(v) {
               self.flow_ae.insert((GValue::Bool(tt()), true_branch.clone()));
               self.push_eval(true_branch.clone(), ctx.clone(), next_ak.clone());
            }
            if matches!(v, GValue::Bool(b) if b.as_ref() == "#f") {
               self.flow_ae.insert((GValue::Bool(ff()), false_branch.clone()));
               self.push_eval(false_branch.clone(), ctx.clone(), next_ak.clone());
            }
         }
         GKont::Callcc { ectx, next_ak } => match v {
            GValue::Closure { e: elam, ctx: ctx_clo } => {
               if let Node::Lam { params, body } = &self.prog.node[elam] {
                  if let Some(x) = params.first() {
                     let body = body.clone();
                     let x = x.clone();
                     self.push_eval(body.clone(), ectx.clone(), next_ak.clone());
                     self.push_val(GAddrV { x, ctx: ectx.clone() }, GValue::Kont(ak.clone()));
                     self.push_copy(ctx_clo.clone(), ectx.clone(), elam.clone());
                     self.flow_ae.insert((v.clone(), body));
                  }
               }
            }
            GValue::Kont(bk) => {
               self.flow_aa.insert((GValue::Kont(bk.clone()), GValue::Kont(ak.clone())));
               self.push_apply(GValue::Kont(ak.clone()), bk.clone());
            }
            _ => {}
         },
         GKont::Arg { args, ctx, ectx, next_ak } => {
            for (pos, earg) in self.prog.call_args[args].clone().into_iter().enumerate() {
               let ak2 = GAddrK { e: earg.clone(), ctx: ctx.clone() };
               self.push_kont(
                  ak2.clone(),
                  GKont::Fn { func: v.clone(), pos: pos as i64, ctx: ectx.clone(), next_ak: next_ak.clone() },
               );
               self.flow_ae.insert((v.clone(), earg.clone()));
               self.push_eval(earg, ctx.clone(), ak2);
            }
         }
         GKont::Fn { func, pos, ctx, next_ak } => match func {
            GValue::Closure { e: elam, ctx: ctx_clo } => {
               if let Node::Lam { params, body } = &self.prog.node[elam] {
                  if let Some(x) = params.get(*pos as usize) {
                     let body = body.clone();
                     let x = x.clone();
                     self.push_eval(body.clone(), ctx.clone(), next_ak.clone());
                     self.push_val(GAddrV { x, ctx: ctx.clone() }, v.clone());
                     self.push_copy(ctx_clo.clone(), ctx.clone(), elam.clone());
                     self.flow_ae.insert((v.clone(), body));
                  }
               }
            }
            GValue::Kont(callcc_kont) if *pos == 0 => {
               self.flow_aa.insert((v.clone(), v.clone()));
               self.push_apply(v.clone(), callcc_kont.clone());
            }
            _ => {}
         },
         GKont::Set { loc, next_ak } => {
            self.push_val(loc.clone(), v.clone());
            self.flow_aa.insert((v.clone(), GValue::Number(-42)));
            self.push_apply(GValue::Number(-42), next_ak.clone());
         }
         GKont::Let { av, ebody, ctx, next_ak } => {
            self.push_val(av.clone(), v.clone());
            self.flow_ae.insert((v.clone(), ebody.clone()));
            self.push_eval(ebody.clone(), ctx.clone(), next_ak.clone());
         }
         GKont::Prim1 { op, e2, ctx, next_ak } => {
            let ak2 = GAddrK { e: e2.clone(), ctx: ctx.clone() };
            self.push_kont(ak2.clone(), GKont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() });
            self.flow_ae.insert((v.clone(), e2.clone()));
            self.push_eval(e2.clone(), ctx.clone(), ak2);
         }
         GKont::Prim2 { op, v1, next_ak } => {
            let pv = GValue::PrimVal {
               op: op.clone(),
               v1: Box::new(v1.clone()),
               v2: Box::new(v.clone()),
            };
            self.flow_aa.insert((v.clone(), pv.clone()));
            self.push_apply(pv, next_ak.clone());
         }
      }
   }
}

/// Run the AAM `m`-CFA analysis on `facts`.
pub fn analyze_aam(facts: &Facts, m: usize) -> AamStats {
   let timing = std::env::var("MCFA_TIMING").is_ok();
   let t0 = std::time::Instant::now();
   let prog = Program::from_facts(facts); // builds the labelled AST and precomputes freevar
   if timing {
      eprintln!("  [aam] setup (Program + freevar): {:.3?}", t0.elapsed());
   }
   let t1 = std::time::Instant::now();
   let mut aam = Aam {
      prog: &prog,
      m,
      sv: HashMap::new(),
      sk: HashMap::new(),
      evals: HashSet::new(),
      applies: HashSet::new(),
      copy: HashSet::new(),
      peek: HashSet::new(),
      flow_ee: HashSet::new(),
      flow_ea: HashSet::new(),
      flow_ae: HashSet::new(),
      flow_aa: HashSet::new(),
      var_reads: HashMap::new(),
      applies_at: HashMap::new(),
      copy_from: HashMap::new(),
      wl: VecDeque::new(),
   };
   aam.run();
   if timing {
      eprintln!("  [aam] worklist fixpoint:          {:.3?}", t1.elapsed());
   }

   AamStats {
      m,
      state_e: aam.evals.len(),
      state_a: aam.applies.len(),
      stored_val: aam.sv.values().map(|s| s.len()).sum(),
      stored_kont: aam.sk.values().map(|s| s.len()).sum(),
      flow_ee: aam.flow_ee.len(),
      flow_ea: aam.flow_ea.len(),
      flow_ae: aam.flow_ae.len(),
      flow_aa: aam.flow_aa.len(),
      peek_ctx: aam.peek.len(),
      copy_ctx: aam.copy.len(),
      flow_ee_edges: aam.flow_ee.into_iter().collect(),
   }
}
