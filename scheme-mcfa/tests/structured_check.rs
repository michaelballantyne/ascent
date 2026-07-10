//! Tests for the structured-syntax variation ([`scheme_mcfa::analyze_structured`]).

use scheme_mcfa::{
   Ast, Facts, GenericStats, StructuredStats, analyze_generic, analyze_structured, church_term, feature_term, to_expr,
   to_expr_labeled, worst_case_term,
};

/// Assert every relation of a structured run has the same size as the flat run.
fn assert_matches_flat(s: &StructuredStats, flat: &GenericStats, what: &str) {
   assert_eq!(s.state_e, flat.state_e, "{what}: state_e");
   assert_eq!(s.state_a, flat.state_a, "{what}: state_a");
   assert_eq!(s.stored_val, flat.stored_val, "{what}: stored_val");
   assert_eq!(s.stored_kont, flat.stored_kont, "{what}: stored_kont");
   assert_eq!(s.flow_ee, flat.flow_ee, "{what}: flow_ee");
   assert_eq!(s.flow_ea, flat.flow_ea, "{what}: flow_ea");
   assert_eq!(s.flow_ae, flat.flow_ae, "{what}: flow_ae");
   assert_eq!(s.flow_aa, flat.flow_aa, "{what}: flow_aa");
   assert_eq!(s.peek_ctx, flat.peek_ctx, "{what}: peek_ctx");
   assert_eq!(s.copy_ctx, flat.copy_ctx, "{what}: copy_ctx");
}

/// On a term with **no duplicate subexpressions**, structural equality
/// coincides with occurrence identity, so even the hash-consed analysis
/// produces exactly the same relation sizes as the flat id-based analysis.
#[test]
fn hashconsed_matches_flat_when_no_duplicate_subterms() {
   let ast = feature_term();
   let flat = analyze_generic(&Facts::from_ast(&ast), 1);
   let s = analyze_structured(&to_expr(&ast), 1);
   assert_matches_flat(&s, &flat, "feature_term m=1");
}

/// The occurrence-labelled tree reproduces the flat analysis' semantics on
/// **any** term — including ones full of duplicate subexpressions — at every
/// `m`.
#[test]
fn labeled_matches_flat_on_any_term() {
   let terms: [(&str, Ast); 3] = [
      ("worst_case_term(6,2,1)", worst_case_term(6, 2, 1)),
      ("church_term(3)", church_term(3)),
      ("twin_call_sites", twin_call_sites_term()),
   ];
   for (name, ast) in &terms {
      let facts = Facts::from_ast(ast);
      let top = to_expr_labeled(ast);
      for m in 0..=2 {
         let flat = analyze_generic(&facts, m);
         let s = analyze_structured(&top, m);
         assert_matches_flat(&s, &flat, &format!("{name} m={m}"));
      }
   }
}

/// On a term **with** duplicate subexpressions (the worst-case family repeats
/// `z`, the identity lambda, etc.), hash-consing conflates the repeated
/// occurrences. On *this* family the conflation only merges states — fewer
/// expression-level facts (`state_e`), identical value-flow — but see
/// [`hashconsing_can_lose_precision`] for the other direction.
#[test]
fn hashconsing_conflates_duplicate_subterms() {
   let ast = worst_case_term(6, 2, 1);
   let flat = analyze_generic(&Facts::from_ast(&ast), 1);
   let s = analyze_structured(&to_expr(&ast), 1);

   // Occurrence multiplicity drops...
   assert!(s.state_e < flat.state_e, "expected hash-consed state_e ({}) < flat ({})", s.state_e, flat.state_e);
   assert!(s.total_derived() <= flat.total_derived());

   // ...but the value-flow the analysis computes is identical.
   assert_eq!(s.stored_val, flat.stored_val, "stored_val");
   assert_eq!(s.flow_ee, flat.flow_ee, "flow_ee");
   assert_eq!(s.flow_aa, flat.flow_aa, "flow_aa");
   assert_eq!(s.copy_ctx, flat.copy_ctx, "copy_ctx");
}

/// Two textually identical call sites in different parts of the program:
///
/// ```scheme
/// (let ((mk (lambda (v) (lambda (u) v))))
///   (let ((f (mk 1)) (g (mk 2)))
///     (let ((r1 ((lambda (h) (h 0)) f))
///           (r2 ((lambda (h) (h 0)) g)))
///       r1)))
/// ```
///
/// The two `(lambda (h) (h 0))` occurrences are structurally equal, so under
/// hash-consing the inner call `(h 0)` is *one* expression and — at `m = 1`,
/// where the contour is just that call — both applications of `f`'s and `g`'s
/// closures share the contour `[(h 0)]`.
fn twin_call_sites_term() -> Ast {
   let apply0 = || Ast::lam(&["h"], Ast::app(Ast::var("h"), vec![Ast::num(0)]));
   Ast::let_(
      vec![("mk", Ast::lam(&["v"], Ast::lam(&["u"], Ast::var("v"))))],
      Ast::let_(
         vec![("f", Ast::app(Ast::var("mk"), vec![Ast::num(1)])), ("g", Ast::app(Ast::var("mk"), vec![Ast::num(2)]))],
         Ast::let_(
            vec![("r1", Ast::app(apply0(), vec![Ast::var("f")])), ("r2", Ast::app(apply0(), vec![Ast::var("g")]))],
            Ast::var("r1"),
         ),
      ),
   )
}

/// Hash-consing is a *coarser abstraction*, not just deduplication: on the
/// twin-call-sites term at `m = 1` the shared contour merges the value
/// addresses of the two calls, cross-wiring `1` into `r2` and `2` into `r1` —
/// so the hash-consed analysis derives strictly *more* `stored_val`/`state_a`
/// facts than the flat/labelled one. (At `m = 2` the enclosing applications —
/// which differ structurally — re-enter the contour and the divergence
/// disappears.)
#[test]
fn hashconsing_can_lose_precision() {
   let ast = twin_call_sites_term();
   let flat = analyze_generic(&Facts::from_ast(&ast), 1);
   let s = analyze_structured(&to_expr(&ast), 1);

   assert!(
      s.stored_val > flat.stored_val,
      "expected hash-consed stored_val ({}) > flat ({}) from cross-wired flows",
      s.stored_val,
      flat.stored_val
   );
   assert!(s.state_a > flat.state_a, "expected hash-consed state_a ({}) > flat ({})", s.state_a, flat.state_a);
}

/// The structured analysis also supports the tunable-`m` variation and
/// terminates at `m = 0`.
#[test]
fn structured_runs_at_m0() {
   let s = analyze_structured(&to_expr(&worst_case_term(5, 2, 0)), 0);
   assert!(s.total_derived() > 0);
}
