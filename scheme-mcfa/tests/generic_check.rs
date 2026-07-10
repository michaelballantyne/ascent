//! Tests for the tunable-`m` variation ([`scheme_mcfa::analyze_generic`]).

use std::collections::BTreeSet;

use scheme_mcfa::{Facts, analyze, analyze_generic, feature_term, worst_case_term};

/// The generic analysis at `m = 1` must produce exactly the same flow graph as
/// the faithful, hard-coded `m = 1` port.
#[test]
fn generic_m1_matches_faithful() {
   for ast in [feature_term(), worst_case_term(5, 2, 1), worst_case_term(6, 3, 0)] {
      let faithful = analyze(&ast);
      let generic = analyze_generic(&Facts::from_ast(&ast), 1);

      let faithful_edges: BTreeSet<_> = faithful.flow_ee.iter().cloned().collect();
      let generic_edges: BTreeSet<_> = generic.flow_ee_edges.iter().cloned().collect();
      assert_eq!(faithful_edges, generic_edges, "flow_ee differs between faithful and generic m=1");

      assert_eq!(faithful.state_e.len(), generic.state_e, "state_e size differs");
      assert_eq!(faithful.state_a.len(), generic.state_a, "state_a size differs");
      assert_eq!(faithful.stored_val.len(), generic.stored_val, "stored_val size differs");
      assert_eq!(faithful.stored_kont.len(), generic.stored_kont, "stored_kont size differs");
   }
}

/// The paper's central phenomena, reproduced on our worst-case term family:
///
/// 1. Insufficient polyvariance blows up: with no padding, `m ∈ {0,1}`
///    conflate the calls to `f` and explode, while `m = 2` is precise (orders
///    of magnitude smaller).
/// 2. Padding defeats a given polyvariance: adding one identity-padding layer
///    pushes the conflation past `m = 2`, so the `m = 2` analysis that was
///    precise now explodes.
#[test]
fn polyvariance_and_padding_phenomena() {
   // (1) precision kicks in at m = 2 when there is no padding.
   let unpadded = Facts::from_ast(&worst_case_term(8, 2, 0));
   let m0 = analyze_generic(&unpadded, 0).total_derived();
   let m1 = analyze_generic(&unpadded, 1).total_derived();
   let m2 = analyze_generic(&unpadded, 2).total_derived();
   assert!(m1 > 5 * m2, "expected m=1 ({m1}) to blow up relative to precise m=2 ({m2})");
   assert!(m0 >= m2, "expected m=0 ({m0}) to be no smaller than m=2 ({m2})");

   // (2) one layer of padding makes the previously-precise m=2 explode.
   let padded = Facts::from_ast(&worst_case_term(8, 2, 1));
   let m2_padded = analyze_generic(&padded, 2).total_derived();
   assert!(m2_padded > 5 * m2, "expected padded m=2 ({m2_padded}) to explode vs unpadded m=2 ({m2})");
}
