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

/// Like [`worst_case_term`] but using only single-argument lambdas,
/// single-argument applications, and nested single-binding `let`s, so the term
/// can be represented by a fixed-arity syntax ADT (no list encoding). Used by
/// the Soufflé ADT-syntax experiment (`souffle/mcfa_adt.dl`), which needs a
/// non-list ADT. The blow-up mechanism is the same as [`worst_case_term`].
pub fn worst_case_term_single(n_calls: usize, k_plus: usize, padding: usize) -> Ast {
   let n_calls = n_calls.max(1);
   let k_plus = k_plus.max(1);

   let inner = Ast::app(Ast::lam(&["x"], plus_chain(k_plus)), vec![identity()]);
   let f_lambda = Ast::lam(&["z"], pad(inner, padding));

   // nested single-binding lets: (let ((b0 (f 0))) (let ((b1 (f 1))) ... b0))
   let mut body = Ast::var("b0");
   for i in (0..n_calls).rev() {
      let name = format!("b{i}");
      body = Ast::let_(
         vec![(name.as_str(), Ast::app(Ast::var("f"), vec![Ast::num(i as i64)]))],
         body,
      );
   }
   Ast::app(Ast::lam(&["f"], body), vec![f_lambda])
}

/// A "realistic" higher-order benchmark: Church-encoded natural-number
/// arithmetic. Builds the numerals `0..=n` with the Church successor, sums them
/// with Church `plus`, and reads the result out by applying it to `add1` and
/// `0`. Unlike the adversarial worst-case family, this is an ordinary
/// functional program — but it is intensely higher-order (every number is a
/// function, and `succ`/`plus`/`add1` are shared, so many closures flow to the
/// same call sites), which is exactly what makes CFA work.
///
/// ```scheme
/// (let ((zero (lambda (f) (lambda (x) x)))
///       (succ (lambda (n) (lambda (f) (lambda (x) (f ((n f) x))))))
///       (plus (lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))))
///       (idf  (lambda (y) y)))
///   ((  (plus (... (plus n0 n1) ...) nN)  idf) base))
/// ```
///
/// We read the numeral out by applying it to the *identity* function and a base
/// value. Applying identity any number of times keeps the value bounded, so the
/// abstract value domain stays finite and the analysis is tractable — the
/// workload is the (still substantial) higher-order *closure* flow through the
/// shared `succ`/`plus`/`idf` lambdas, which is what CFA is about.
///
/// (Using an arithmetic read-out such as `(lambda (y) (+ y 1))` instead makes
/// the analysis build an unbounded tower of `PrimVal`s and blow up at every `m`
/// — a faithful demonstration that `m`-CFA is intractable on natural
/// higher-order arithmetic, but useless as a bounded benchmark.)
pub fn church_term(n: usize) -> Ast {
   let n = n.max(1);
   let ap1 = |f: Ast, a: Ast| Ast::app(f, vec![a]); // curried single-arg application

   let zero = Ast::lam(&["f"], Ast::lam(&["x"], Ast::var("x")));
   let succ = Ast::lam(
      &["n"],
      Ast::lam(&["f"], Ast::lam(&["x"], ap1(Ast::var("f"), ap1(ap1(Ast::var("n"), Ast::var("f")), Ast::var("x"))))),
   );
   let plus = Ast::lam(
      &["m"],
      Ast::lam(
         &["n"],
         Ast::lam(
            &["f"],
            Ast::lam(&["x"], ap1(ap1(Ast::var("m"), Ast::var("f")), ap1(ap1(Ast::var("n"), Ast::var("f")), Ast::var("x")))),
         ),
      ),
   );
   let idf = Ast::lam(&["y"], Ast::var("y"));

   // Church numerals 0..=n, each built with `succ`.
   let mut nums = vec![Ast::var("zero")];
   for _ in 1..=n {
      let prev = nums.last().unwrap().clone();
      nums.push(ap1(Ast::var("succ"), prev));
   }

   // Sum them all with `plus`.
   let mut acc = nums[0].clone();
   for num in nums.iter().skip(1) {
      acc = ap1(ap1(Ast::var("plus"), acc), num.clone());
   }

   // Read out the resulting numeral: ((acc idf) 0).
   let readout = ap1(ap1(acc, Ast::var("idf")), Ast::num(0));

   Ast::let_(vec![("zero", zero), ("succ", succ), ("plus", plus), ("idf", idf)], readout)
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
