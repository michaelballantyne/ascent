//! A tiny AST for the subset of Scheme analyzed in
//! "So You Want To Analyze Scheme Programs With Datalog?" (Silverman, Sun,
//! Micinski, Gilray; Scheme Workshop 2021), plus a generator for the
//! worst-case term family used in the paper's evaluation (Section 5, Fig. 12).
//!
//! The grammar (Fig. 1 of the paper) is:
//!
//! ```text
//! e ::= ae | (if e e e) | (set! x e) | (call/cc e) | let
//!     | (op e e) | (e e e ...)
//! ae ::= x | lam | b | n
//! lam ::= (lambda (x ...) e)
//! let ::= (let ((x e) ...) e)
//! ```

use std::sync::Arc;

/// Interned symbol / identifier. The paper uses Soufflé `symbol`s for both
/// expression ids and variable names, so we use one type for both.
pub type Sym = Arc<str>;

pub fn sym(s: &str) -> Sym { Arc::from(s) }

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ast {
   Var(Sym),
   Num(i64),
   Bool(bool),
   /// `(lambda (x ...) body)`
   Lam(Vec<Sym>, Box<Ast>),
   /// `(f a ...)`
   App(Box<Ast>, Vec<Ast>),
   /// `(if g t f)`
   If(Box<Ast>, Box<Ast>, Box<Ast>),
   /// `(let ((x e) ...) body)`
   Let(Vec<(Sym, Ast)>, Box<Ast>),
   /// `(set! x e)`
   Set(Sym, Box<Ast>),
   /// `(call/cc e)`
   Callcc(Box<Ast>),
   /// `(op e0 e1)` — a binary primitive application
   Prim(Sym, Box<Ast>, Box<Ast>),
}

impl Ast {
   pub fn var(x: &str) -> Ast { Ast::Var(sym(x)) }
   pub fn num(n: i64) -> Ast { Ast::Num(n) }
   pub fn bool(b: bool) -> Ast { Ast::Bool(b) }
   pub fn lam(params: &[&str], body: Ast) -> Ast {
      Ast::Lam(params.iter().map(|p| sym(p)).collect(), Box::new(body))
   }
   pub fn app(f: Ast, args: Vec<Ast>) -> Ast { Ast::App(Box::new(f), args) }
   pub fn if_(g: Ast, t: Ast, f: Ast) -> Ast {
      Ast::If(Box::new(g), Box::new(t), Box::new(f))
   }
   pub fn let_(binds: Vec<(&str, Ast)>, body: Ast) -> Ast {
      Ast::Let(binds.into_iter().map(|(x, e)| (sym(x), e)).collect(), Box::new(body))
   }
   pub fn set(x: &str, e: Ast) -> Ast { Ast::Set(sym(x), Box::new(e)) }
   pub fn callcc(e: Ast) -> Ast { Ast::Callcc(Box::new(e)) }
   pub fn prim(op: &str, e0: Ast, e1: Ast) -> Ast {
      Ast::Prim(sym(op), Box::new(e0), Box::new(e1))
   }
}

/// The identity function `(lambda (ix) ix)`.
fn identity() -> Ast { Ast::lam(&["ix"], Ast::var("ix")) }

/// A right-nested chain of `k` `+` applications over the free variable `z`:
/// `(+ z (+ z ... (+ z z)))`.
fn plus_chain(k: usize) -> Ast {
   if k <= 1 {
      Ast::prim("+", Ast::var("z"), Ast::var("z"))
   } else {
      Ast::prim("+", Ast::var("z"), plus_chain(k - 1))
   }
}

/// Wrap `t` in `p` layers of "padding": each layer binds a fresh variable to
/// the identity function and then evaluates `t`, ignoring the bound variable.
/// In `m`-CFA this pushes the context of the enclosing binding out of the
/// (length-`m`) contour, forcing conflation — this is the trick from Van Horn's
/// dissertation, adapted for `m`-CFA in Section 5.1 of the paper.
fn pad(mut t: Ast, p: usize) -> Ast {
   for j in 0..p {
      let pj = format!("pad{j}");
      t = Ast::app(Ast::lam(&[&pj], t), vec![identity()]);
   }
   t
}

/// The worst-case term family from the paper's evaluation (Fig. 11 & 12).
///
/// * `n_calls` — the number of calls to `f` (the `N` in the paper's `N/K`).
/// * `k_plus`  — the number of `+` invocations (the `K` in the paper's `N/K`).
/// * `padding` — the amount of identity-function padding (0/1/2 in Table 1).
///
/// ```text
/// ((lambda (f)
///    (let ((b0 (f 0)) (b1 (f 1)) ... (b_{N-1} (f (N-1))))
///      b0))
///  (lambda (z)
///    PAD^padding[ ((lambda (x) (+ z (+ z ...))) (lambda (ix) ix)) ]))
/// ```
///
/// `f` is bound to `(lambda (z) ...)` and applied to `N` distinct constants.
/// With too little polyvariance/padding these calls are conflated, so `z`
/// takes `N` abstract values which then combine through the `K` nested `+`s,
/// producing the `PrimVal` blow-up that drives the analysis' worst-case cost.
pub fn worst_case_term(n_calls: usize, k_plus: usize, padding: usize) -> Ast {
   let n_calls = n_calls.max(1);
   let k_plus = k_plus.max(1);

   let inner = Ast::app(Ast::lam(&["x"], plus_chain(k_plus)), vec![identity()]);
   let f_lambda = Ast::lam(&["z"], pad(inner, padding));

   let mut binds: Vec<(&str, Ast)> = Vec::new();
   let names: Vec<String> = (0..n_calls).map(|i| format!("b{i}")).collect();
   for (i, name) in names.iter().enumerate() {
      binds.push((name.as_str(), Ast::app(Ast::var("f"), vec![Ast::num(i as i64)])));
   }
   let let_expr = Ast::let_(binds, Ast::var("b0"));

   Ast::app(Ast::lam(&["f"], let_expr), vec![f_lambda])
}

/// A small term exercising every language feature (and hence every analysis
/// rule family): `let`, `lambda`, `var`, `call`, `if`, `set!`, `call/cc`
/// (both capturing and invoking the continuation), booleans, and a binary
/// primitive. Used by the Soufflé cross-check test.
///
/// ```text
/// (let ((kv (call/cc (lambda (c) (c 5)))))
///   (let ((a ((lambda (x) x) #t)))
///     (if a (set! a 7) (+ kv 1))))
/// ```
pub fn feature_term() -> Ast {
   let callcc = Ast::callcc(Ast::lam(&["c"], Ast::app(Ast::var("c"), vec![Ast::num(5)])));
   let a_bind = Ast::app(Ast::lam(&["x"], Ast::var("x")), vec![Ast::bool(true)]);
   let inner_if = Ast::if_(
      Ast::var("a"),
      Ast::set("a", Ast::num(7)),
      Ast::prim("+", Ast::var("kv"), Ast::num(1)),
   );
   Ast::let_(
      vec![("kv", callcc)],
      Ast::let_(vec![("a", a_bind)], inner_if),
   )
}
