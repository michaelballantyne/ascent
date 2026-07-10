//! **Variation: syntax as structured data.**
//!
//! The paper's Appendix A represents *values* and *continuations* as Soufflé
//! ADTs, but flattens *syntax* into id-keyed input relations (`lambda`, `call`,
//! `if`, `let`, `var`, ...) that rules join on by expression id. In Ascent a
//! relation column can be any `Clone + Eq + Hash` value, and rule bodies can
//! pattern-match it — so we can represent syntax the same way the paper
//! represents values and continuations: as a recursive [`Expr`]. The flat
//! `lambda`/`call`/`if`/... relations disappear entirely; every rule instead
//! matches on the structure of the expression in the current `state_e`.
//!
//! (Why doesn't the paper do this in Soufflé? Not join cost: Soufflé
//! hash-conses ADTs, and the `souffle/mcfa_adt.dl` experiment in this crate
//! shows ADT-carried syntax is *not* slower there. The friction is
//! expressiveness — Soufflé rejects wildcards inside an ADT branch match, and
//! variable-arity forms (multi-argument lambdas, multi-binding `let`s) have no
//! natural fixed-arity ADT encoding. See the README.)
//!
//! ## Two identities for syntax
//!
//! Syntax nodes are labelled: a [`Node`] pairs an [`Expr`] with a label, and
//! `Eq`/`Hash` are keyed on the label alone. Node comparison is therefore O(1),
//! and the *labeling scheme* decides what "the same expression" means:
//!
//! * [`to_expr`] **hash-conses** — structurally equal subterms get the same
//!   label (and share one allocation). This is the identity Soufflé's interned
//!   ADTs have, so it is the mode comparable to `souffle/mcfa_adt.dl`.
//! * [`to_expr_labeled`] labels every *occurrence* freshly — recovering the
//!   id-based port's semantics exactly: on any term, the analysis agrees with
//!   the flat analysis relation-for-relation (`tests/structured_check.rs`).
//!
//! ## Semantic note: hash-consing is a coarser abstraction
//!
//! Under [`to_expr`], structurally identical subterms are *identified*. This is
//! not mere deduplication: contexts ([`SCtx`]) and addresses are built from
//! expressions, so two textually identical binding sites in different parts of
//! the program share a contour entry — structural identification weakens the
//! analysis' polyvariance. Merged continuation/value addresses can also
//! cross-wire flows. Relative to the occurrence-labelled analysis the
//! hash-consed one may therefore derive *fewer* facts (states merged) or *more*
//! (spurious flows through shared addresses); `tests/structured_check.rs`
//! exhibits both directions. On a term with no duplicate subexpressions the two
//! labelings coincide exactly.

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use ascent::ascent_run;

use crate::ast::{Ast, Sym};
use crate::{ff, tt};

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

/// A labelled syntax node. `Eq`/`Hash` are keyed on the label alone, so node
/// comparison is O(1) and the labeling chosen at construction decides the
/// identity of syntax: hash-consed ([`to_expr`]) or per-occurrence
/// ([`to_expr_labeled`]).
#[derive(Clone)]
pub struct Node {
   label: u32,
   pub expr: Expr,
}

impl PartialEq for Node {
   fn eq(&self, other: &Self) -> bool { self.label == other.label }
}
impl Eq for Node {}
impl std::hash::Hash for Node {
   fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.label.hash(state) }
}
impl fmt::Debug for Node {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.expr.fmt(f) }
}

/// A (shared) labelled expression.
pub type E = Arc<Node>;

/// [`Ast`] → [`E`] conversion, parameterized by the labeling scheme.
struct Conv {
   next: u32,
   /// `Some` ⇒ hash-cons (one label per distinct structure);
   /// `None` ⇒ a fresh label per occurrence.
   table: Option<HashMap<Expr, E>>,
}

impl Conv {
   /// Label `expr`. Note the interner map compares `Expr`s shallowly — one
   /// variant tag plus child *labels* — so hash-consing is O(1) per node.
   fn mk(&mut self, expr: Expr) -> E {
      match &mut self.table {
         Some(table) => match table.get(&expr) {
            Some(e) => e.clone(),
            None => {
               let node = Arc::new(Node { label: self.next, expr: expr.clone() });
               self.next += 1;
               table.insert(expr, node.clone());
               node
            },
         },
         None => {
            let node = Arc::new(Node { label: self.next, expr });
            self.next += 1;
            node
         },
      }
   }

   fn conv(&mut self, ast: &Ast) -> E {
      let expr = match ast {
         Ast::Var(x) => Expr::Var(x.clone()),
         Ast::Num(n) => Expr::Num(*n),
         Ast::Bool(b) => Expr::Bool(if *b { tt() } else { ff() }),
         Ast::Lam(ps, b) => Expr::Lam(ps.clone(), self.conv(b)),
         Ast::App(f, args) => Expr::App(self.conv(f), args.iter().map(|a| self.conv(a)).collect()),
         Ast::If(g, t, f) => Expr::If(self.conv(g), self.conv(t), self.conv(f)),
         Ast::Let(bs, b) => Expr::Let(bs.iter().map(|(x, e)| (x.clone(), self.conv(e))).collect(), self.conv(b)),
         Ast::Set(x, e) => Expr::Set(x.clone(), self.conv(e)),
         Ast::Callcc(e) => Expr::Callcc(self.conv(e)),
         Ast::Prim(op, a, b) => Expr::Prim(op.clone(), self.conv(a), self.conv(b)),
      };
      self.mk(expr)
   }
}

/// Convert the surface [`Ast`] into a **hash-consed** [`Expr`] tree:
/// structurally equal subterms share one label, so the analysis *identifies*
/// structurally identical occurrences (the identity Soufflé ADTs have).
pub fn to_expr(ast: &Ast) -> E { Conv { next: 0, table: Some(HashMap::new()) }.conv(ast) }

/// Convert the surface [`Ast`] into a per-**occurrence**-labelled [`Expr`]
/// tree: every node is distinct, recovering the id-based (flat) analysis'
/// occurrence semantics exactly.
pub fn to_expr_labeled(ast: &Ast) -> E { Conv { next: 0, table: None }.conv(ast) }

/// `context` — the most-recent (up to) `m` binding-site expressions.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SCtx(pub Vec<E>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SAddrK {
   pub e: E,
   pub ctx: SCtx,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SAddrV {
   pub x: Sym,
   pub ctx: SCtx,
}

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
/// to Appendix A). Memoized per node label, so hash-consed trees compute each
/// distinct structure once. (Shared with the direct-AAM engine in
/// [`crate::aam`] so both engines agree on the copy semantics.)
pub(crate) fn free_vars(e: &E, cache: &mut HashMap<E, Rc<Vec<Sym>>>) -> Rc<Vec<Sym>> {
   if let Some(v) = cache.get(e) {
      return v.clone();
   }
   let set: BTreeSet<Sym> = match &e.expr {
      Expr::Var(x) => std::iter::once(x.clone()).collect(),
      Expr::Num(_) | Expr::Bool(_) => BTreeSet::new(),
      Expr::Lam(ps, b) => {
         let bound: BTreeSet<&Sym> = ps.iter().collect();
         free_vars(b, cache).iter().filter(|x| !bound.contains(x)).cloned().collect()
      },
      Expr::App(f, args) => {
         let mut s: BTreeSet<Sym> = free_vars(f, cache).iter().cloned().collect();
         for a in args {
            s.extend(free_vars(a, cache).iter().cloned());
         }
         s
      },
      Expr::Prim(_, a, b) => {
         let mut s: BTreeSet<Sym> = free_vars(a, cache).iter().cloned().collect();
         s.extend(free_vars(b, cache).iter().cloned());
         s
      },
      Expr::If(g, t, f) => {
         let mut s: BTreeSet<Sym> = free_vars(g, cache).iter().cloned().collect();
         s.extend(free_vars(t, cache).iter().cloned());
         s.extend(free_vars(f, cache).iter().cloned());
         s
      },
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
      },
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
      self.state_e
         + self.state_a
         + self.stored_val
         + self.stored_kont
         + self.flow_ee
         + self.flow_ea
         + self.flow_ae
         + self.flow_aa
   }
}

/// The machine and flow relations of a structured run, as plain data — kept so
/// the direct-AAM engine ([`crate::aam`]) can be checked *content*-equal to the
/// Datalog fixpoint (`tests/aam_check.rs`), not merely size-equal.
pub struct StructuredRun {
   pub stats: StructuredStats,
   pub state_e: Vec<(E, SCtx, SAddrK)>,
   pub state_a: Vec<(SValue, SAddrK)>,
   pub stored_val: Vec<(SAddrV, SValue)>,
   pub stored_kont: Vec<(SAddrK, SKont)>,
   pub flow_ee: Vec<(E, E)>,
   pub flow_ea: Vec<(E, SValue)>,
   pub flow_ae: Vec<(SValue, E)>,
   pub flow_aa: Vec<(SValue, SValue)>,
}

/// Run `m`-CFA on a structured [`Expr`], driving control flow by matching on
/// syntax rather than joining flat id-relations. What "the same expression"
/// means is decided by how `top` was built: [`to_expr`] identifies structurally
/// equal subterms, [`to_expr_labeled`] keeps every occurrence distinct (and
/// then reproduces the flat analysis exactly).
pub fn analyze_structured(top: &E, m: usize) -> StructuredStats { analyze_structured_run(top, m).stats }

/// Like [`analyze_structured`], but returning the relations themselves.
pub fn analyze_structured_run(top: &E, m: usize) -> StructuredRun {
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
         if matches!(&e.expr, Expr::App(..) | Expr::Let(..) | Expr::Callcc(..) | Expr::Lam(..));

      // copy_ctx: copy the free-variable bindings between contexts.
      // (`fvs` covers every subterm of `top`, and every expression reaching
      // `copy_ctx` is such a subterm, so the lookup cannot miss.)
      stored_val(SAddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
         copy_ctx(from, to, e),
         for fv in fvs.get(e).unwrap().iter(),
         stored_val(SAddrV { x: fv.clone(), ctx: from.clone() }, v);

      // E-If
      state_e(eg.clone(), ctx.clone(), SAddrK { e: eg.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: eg.clone(), ctx: ctx.clone() },
                  SKont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), eg.clone()) <--
         state_e(e, ctx, ak), if let Expr::If(eg, et, ef) = &e.expr;

      // E-C/cc
      state_e(elam.clone(), ctx.clone(), SAddrK { e: elam.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: elam.clone(), ctx: ctx.clone() },
                  SKont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), elam.clone()) <--
         state_e(e, ctx, ak), if let Expr::Callcc(elam) = &e.expr, peek_ctx(e, ctx, ectx);

      // E-Set!
      state_e(esub.clone(), ctx.clone(), SAddrK { e: esub.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: esub.clone(), ctx: ctx.clone() },
                  SKont::Set { loc: SAddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
      flow_ee(e.clone(), esub.clone()) <--
         state_e(e, ctx, ak), if let Expr::Set(x, esub) = &e.expr;

      // E-Call
      state_e(efunc.clone(), ctx.clone(), SAddrK { e: efunc.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: efunc.clone(), ctx: ctx.clone() },
                  SKont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), efunc.clone()) <--
         state_e(e, ctx, ak), if let Expr::App(efunc, eargs) = &e.expr, peek_ctx(e, ctx, ectx);

      // E-Let
      state_e(ebnd.clone(), ctx.clone(), SAddrK { e: ebnd.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: ebnd.clone(), ctx: ctx.clone() },
                  SKont::Let { av: SAddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
      copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
      flow_ee(e.clone(), ebnd.clone()) <--
         state_e(e, ctx, ak),
         if let Expr::Let(binds, ebody) = &e.expr,
         peek_ctx(e, ctx, ectx),
         for (x, ebnd) in binds.iter();

      // E-Prim
      state_e(e0.clone(), ctx.clone(), SAddrK { e: e0.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: e0.clone(), ctx: ctx.clone() },
                  SKont::Prim1 { op: op.clone(), e2: e1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), e0.clone()) <--
         state_e(e, ctx, ak), if let Expr::Prim(op, e0, e1) = &e.expr;

      // atomic evaluation
      state_a(SValue::Number(*n), ak.clone()),
      flow_ea(e.clone(), SValue::Number(*n)) <--
         state_e(e, _, ak), if let Expr::Num(n) = &e.expr;

      state_a(SValue::Bool(b.clone()), ak.clone()),
      flow_ea(e.clone(), SValue::Bool(b.clone())) <--
         state_e(e, _, ak), if let Expr::Bool(b) = &e.expr;

      state_a(SValue::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
      flow_ea(e.clone(), SValue::Closure { e: e.clone(), ctx: ctx.clone() }) <--
         state_e(e, ctx, ak), if matches!(&e.expr, Expr::Lam(..));

      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         state_e(e, ctx, ak),
         if let Expr::Var(x) = &e.expr,
         stored_val(SAddrV { x: x.clone(), ctx: ctx.clone() }, v);

      // A-IfT / A-IfF
      state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(tt()), et.clone()) <--
         state_a(v, ak), if sif_true(v),
         stored_kont(ak, ?SKont::If { true_branch: et, ctx: ctx_k, next_ak, .. });

      state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(ff()), ef.clone()) <--
         state_a(?SValue::Bool(b), ak), if b.as_ref() == "#f",
         stored_kont(ak, ?SKont::If { false_branch: ef, ctx: ctx_k, next_ak, .. });

      // A-C/cc (closure applied to captured continuation)
      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(SAddrV { x: x.clone(), ctx: ectx.clone() }, SValue::Kont(ak.clone())),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(SValue::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
         state_a(?SValue::Closure { e: elam, ctx: ctx_clo }, ak),
         stored_kont(ak, ?SKont::Callcc { ectx, next_ak }),
         if let Expr::Lam(params, ebody) = &elam.expr,
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
         if let Expr::Lam(params, ebody) = &elam.expr,
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

   let mut prog = prog;
   let stats = StructuredStats {
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
   };
   StructuredRun {
      stats,
      state_e: std::mem::take(&mut prog.state_e),
      state_a: std::mem::take(&mut prog.state_a),
      stored_val: std::mem::take(&mut prog.stored_val),
      stored_kont: std::mem::take(&mut prog.stored_kont),
      flow_ee: std::mem::take(&mut prog.flow_ee),
      flow_ea: std::mem::take(&mut prog.flow_ea),
      flow_ae: std::mem::take(&mut prog.flow_ae),
      flow_aa: std::mem::take(&mut prog.flow_aa),
   }
}
