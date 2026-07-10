//! Tests for the structured-syntax variation ([`scheme_mcfa::analyze_structured`]).

use scheme_mcfa::{Facts, analyze_generic, analyze_structured, feature_term, to_expr, worst_case_term};

/// On a term with **no duplicate subexpressions**, structural equality
/// coincides with occurrence identity, so the structured-syntax analysis
/// produces exactly the same relation sizes as the flat id-based analysis.
#[test]
fn structured_matches_flat_when_no_duplicate_subterms() {
   let ast = feature_term();
   let flat = analyze_generic(&Facts::from_ast(&ast), 1);
   let s = analyze_structured(&to_expr(&ast), 1);

   assert_eq!(s.state_e, flat.state_e, "state_e");
   assert_eq!(s.state_a, flat.state_a, "state_a");
   assert_eq!(s.stored_val, flat.stored_val, "stored_val");
   assert_eq!(s.stored_kont, flat.stored_kont, "stored_kont");
   assert_eq!(s.flow_ee, flat.flow_ee, "flow_ee");
   assert_eq!(s.flow_ea, flat.flow_ea, "flow_ea");
   assert_eq!(s.flow_ae, flat.flow_ae, "flow_ae");
   assert_eq!(s.flow_aa, flat.flow_aa, "flow_aa");
   assert_eq!(s.peek_ctx, flat.peek_ctx, "peek_ctx");
   assert_eq!(s.copy_ctx, flat.copy_ctx, "copy_ctx");
}

/// On a term **with** duplicate subexpressions (the worst-case family repeats
/// `z`, the identity lambda, etc.), structural equality conflates the repeated
/// occurrences: the structured analysis derives fewer expression-level facts
/// (`state_e`), while the value-flow content it computes is unchanged.
#[test]
fn structured_conflates_duplicate_subterms() {
   let ast = worst_case_term(6, 2, 1);
   let flat = analyze_generic(&Facts::from_ast(&ast), 1);
   let s = analyze_structured(&to_expr(&ast), 1);

   // Occurrence multiplicity drops...
   assert!(s.state_e < flat.state_e, "expected structured state_e ({}) < flat ({})", s.state_e, flat.state_e);
   assert!(s.total_derived() <= flat.total_derived());

   // ...but the value-flow the analysis computes is identical.
   assert_eq!(s.stored_val, flat.stored_val, "stored_val");
   assert_eq!(s.flow_ee, flat.flow_ee, "flow_ee");
   assert_eq!(s.flow_aa, flat.flow_aa, "flow_aa");
   assert_eq!(s.copy_ctx, flat.copy_ctx, "copy_ctx");
}

/// The structured analysis also supports the tunable-`m` variation and
/// terminates at `m = 0`.
#[test]
fn structured_runs_at_m0() {
   let s = analyze_structured(&to_expr(&worst_case_term(5, 2, 0)), 0);
   assert!(s.total_derived() > 0);
}
