//! Executable evidence for the expressiveness verdicts in
//! `src/slog_style.rs`. See that file's doc comment for the write-up this
//! test suite backs.

use scheme_mcfa_plusplus::slog_style::baseline::{self, Tag};

#[test]
fn baseline_ids_are_dense_and_unique() {
    let prog = baseline::run(vec![(1, 2), (2, 3), (3, 4), (1, 4)]);

    let mut edge_ids: Vec<usize> = prog.edge_id.iter().map(|(_, _, id)| *id).collect();
    edge_ids.sort();
    assert_eq!(edge_ids, (0..prog.edge.len()).collect::<Vec<_>>(), "edge ids should be dense 0..N");

    let mut path_ids: Vec<usize> = prog.path_id.iter().map(|(_, _, id)| *id).collect();
    path_ids.sort();
    assert_eq!(path_ids, (0..prog.path.len()).collect::<Vec<_>>(), "path ids should be dense 0..N");
}

#[test]
fn baseline_path_length_matches_independent_depth_recomputation() {
    let prog = baseline::run(vec![(1, 2), (2, 3), (3, 4), (1, 4)]);
    let expected = baseline::expected_depths(&prog);

    assert!(!expected.is_empty());
    let mut checked = 0;
    for tag in expected.keys() {
        let got = baseline::path_length_of(&prog, tag)
            .unwrap_or_else(|| panic!("no path_length answer for {tag:?}"));
        assert_eq!(got, expected[tag], "path_length disagreed with hand recomputation for {tag:?}");
        checked += 1;
    }
    // sanity: every edge (depth 1) and every path (depth >= 2) got checked.
    assert_eq!(checked, prog.edge.len() + prog.path.len());
    assert!(expected.values().any(|&d| d == 1), "expected at least one depth-1 (edge) entry");
    assert!(expected.values().any(|&d| d >= 2), "expected at least one depth>=2 (path) entry, i.e. TC actually nested");
}

#[test]
fn baseline_tag_edge_edges_all_have_length_one() {
    let prog = baseline::run(vec![(1, 2), (2, 3)]);
    for (_x, _y, eid) in prog.edge_id.iter().cloned() {
        let len = baseline::path_length_of(&prog, &Tag("edge", eid)).unwrap();
        assert_eq!(len, 1);
    }
}

// ---------------------------------------------------------------------------
// relation ID applied naively to syntax: hash-consing pitfall
// ---------------------------------------------------------------------------

use scheme_mcfa_plusplus::slog_style::mcfa_frag;

#[test]
fn hash_cons_pitfall_two_occurrences_of_same_name_collapse_to_one_id() {
    let prog = mcfa_frag::hash_cons_pitfall_probe();
    // Two *occurrences* of the variable name "w" (as if two distinct `w`
    // leaves appeared in different places in a source term) were fed in --
    // a per-occurrence ("to_expr_labeled"-style) encoding would assign them
    // two different ids. `relation ID` on a plain-content relation instead
    // hash-conses: exactly one row, exactly one id.
    assert_eq!(prog.probed_var.len(), 1, "relation ID hash-consed the two occurrences into one row");
    assert_eq!(prog.probed_var_id.len(), 1, "...and therefore minted only one id, not two");
}

// ---------------------------------------------------------------------------
// mCFA fragment: cross-check against scheme_mcfa::structured::analyze_structured_run
// at m = 0, on three tiny terms (var/lambda(1-ary)/call(1-ary)/if only).
// ---------------------------------------------------------------------------

use scheme_mcfa::ast::{Ast, Sym};
use scheme_mcfa::structured::{self, to_expr_labeled, StructuredRun};
use std::collections::HashSet;

fn structured_closure_count(run: &StructuredRun) -> usize {
    let mut set: HashSet<structured::SValue> = HashSet::new();
    for (v, _ak) in &run.state_a {
        if matches!(v, structured::SValue::Closure { .. }) {
            set.insert(v.clone());
        }
    }
    set.len()
}

fn structured_closure_bindings(run: &StructuredRun) -> Vec<(Sym, Sym)> {
    let mut out = vec![];
    for (addr, v) in &run.stored_val {
        if let structured::SValue::Closure { e, .. } = v {
            if let structured::Expr::Lam(params, _) = &e.expr {
                out.push((addr.x.clone(), params[0].clone()));
            }
        }
    }
    out.sort();
    out
}

fn structured_final_closure_param(run: &StructuredRun) -> Option<Sym> {
    let mt_ak = run.stored_kont.iter().find(|(_ak, k)| matches!(k, structured::SKont::MT))?.0.clone();
    let (v, _ak) = run.state_a.iter().find(|(_v, ak)| *ak == mt_ak)?;
    if let structured::SValue::Closure { e, .. } = v {
        if let structured::Expr::Lam(params, _) = &e.expr {
            return Some(params[0].clone());
        }
    }
    None
}

fn mcfa_frag_closure_bindings_sorted(prog: &mcfa_frag::McfaFrag) -> Vec<(Sym, Sym)> {
    let mut v = mcfa_frag::closure_bindings(prog);
    v.sort();
    v
}

fn mcfa_frag_final_closure_param(prog: &mcfa_frag::McfaFrag) -> Option<Sym> {
    match mcfa_frag::final_result(prog) {
        Some(mcfa_frag::Value::Closure(param, _body)) => Some(param),
        _ => None,
    }
}

/// `((lambda (x) x) (lambda (y) y))`: identity applied to identity. Two
/// distinct closures created (the outer and inner lambdas); `x` bound to
/// `Closure(y)`; result is `Closure(y)`.
fn term1() -> Ast { Ast::app(Ast::lam(&["x"], Ast::var("x")), vec![Ast::lam(&["y"], Ast::var("y"))]) }

/// `((lambda (f) (f (lambda (z) z))) (lambda (x) x))`: three distinct
/// closures; `f` bound to `Closure(x)`, `x` bound to `Closure(z)`; result is
/// `Closure(z)`.
fn term2() -> Ast {
    Ast::app(
        Ast::lam(&["f"], Ast::app(Ast::var("f"), vec![Ast::lam(&["z"], Ast::var("z"))])),
        vec![Ast::lam(&["x"], Ast::var("x"))],
    )
}

/// `(if #t (lambda (a) a) (lambda (b) b))`: only the then-branch is ever
/// reached, so exactly one distinct closure is created, no variable is ever
/// bound, and the result is `Closure(a)`.
fn term3() -> Ast { Ast::if_(Ast::bool(true), Ast::lam(&["a"], Ast::var("a")), Ast::lam(&["b"], Ast::var("b"))) }

fn cross_check(ast: &Ast, expected_closure_count: usize, expected_final_param: Option<&str>) {
    let frag_prog = mcfa_frag::run_frag(ast);
    let structured_run = structured::analyze_structured_run(&to_expr_labeled(ast), 0);

    let frag_count = mcfa_frag::reachable_closure_refs(&frag_prog).len();
    let structured_count = structured_closure_count(&structured_run);
    assert_eq!(frag_count, expected_closure_count, "mcfa_frag distinct-closure count");
    assert_eq!(structured_count, expected_closure_count, "analyze_structured distinct-closure count");
    assert_eq!(frag_count, structured_count, "the two engines disagree on distinct-closure count");

    let frag_bindings = mcfa_frag_closure_bindings_sorted(&frag_prog);
    let structured_bindings = structured_closure_bindings(&structured_run);
    assert_eq!(
        frag_bindings, structured_bindings,
        "the two engines disagree on (var -> bound closure's parameter name)"
    );

    let frag_final = mcfa_frag_final_closure_param(&frag_prog);
    let structured_final = structured_final_closure_param(&structured_run);
    assert_eq!(frag_final.as_deref(), expected_final_param, "mcfa_frag final result");
    assert_eq!(structured_final.as_deref(), expected_final_param, "analyze_structured final result");
}

#[test]
fn mcfa_cross_check_term1_identity_applied_to_identity() { cross_check(&term1(), 2, Some("y")); }

#[test]
fn mcfa_cross_check_term2_nested_closures() { cross_check(&term2(), 3, Some("z")); }

#[test]
fn mcfa_cross_check_term3_if_selects_one_branch() { cross_check(&term3(), 1, Some("a")); }

// ---------------------------------------------------------------------------
// A genuine fork bug: `function`'s answer relation double-uses (moves) the
// return variable for any non-`Copy` return type. Minimal repro (unrelated
// to this crate's `Value`/`Tag` types, to show it's general).
// ---------------------------------------------------------------------------

// The macro invocation below is the entire repro; it must be behind
// `#[ignore]`-adjacent tooling since it's a *compile* failure, not a runtime
// one, so it can't be a `#[test]` that runs -- ascent!{} expands at macro
// time. We therefore keep the repro as source text here (not compiled) and
// pin its exact rustc output, reproduced verbatim on this fork rev
// (4f80fa11a2640379b34d43fe2e673e7375c71c71) by temporarily pasting it into
// `src/slog_style/mcfa_frag.rs` and running
// `cargo build -p scheme-mcfa-plusplus`:
//
// ```rust,ignore
// ascent::ascent! {
//    struct FnBugRepro;
//    relation input(usize);
//    function f(usize) -> String;
//    %f(x) -> ? <-- input(x);
//    %f(?x) -> r <-- let r = format!("n{}", x);
// }
// ```
//
// rustc says (verbatim):
//
// ```text
// error[E0382]: use of moved value: `r`
//    --> scheme-mcfa/plusplus/src/slog_style/mcfa_frag.rs:337:14
//     |
// 337 |    %f(?x) -> r <-- let r = format!("n{}", x);
//     |              ^         - move occurs because `r` has type `String`, which does not implement the `Copy` trait
//     |              |
//     |              value used here after move
//     |
// help: consider cloning the value if the performance cost is acceptable
//     |
// 337 |    %f(?x) -> r.clone() <-- let r = format!("n{}", x);
//     |               ++++++++
// ```
//
// (the suggested fix does not parse: `FunctionCallNode::return_var` is
// `Option<Ident>`, so `r.clone()` is not valid syntax there at all --
// confirmed by hitting the identical error, unprompted, on `mcfa_frag`'s own
// original `function atomic_eval(Tag) -> Value;` design, which is what
// prompted this repro). `atomic_eval` in `mcfa_frag.rs` works around this by
// giving the function a `Copy` return type (`Tag`, a value *ref*) and
// resolving through a separate `value_table` relation instead of returning
// `Value` directly -- see that file's doc comment on `function atomic_eval`.
#[test]
#[ignore = "documents a fork compile-time bug (function w/ non-Copy return type); not runnable, see comment above"]
fn function_with_non_copy_return_type_is_broken() {}


// ---------------------------------------------------------------------------
// The genuine `relation ID`-as-continuation attempt: confirm it actually
// round-trips end to end (mint id, store ref, join back), not just typechecks.
// ---------------------------------------------------------------------------

#[test]
fn if_kont_as_id_relation_round_trips() {
    let prog = mcfa_frag::if_kont_as_id_relation_probe();
    assert_eq!(prog.if_kont_row.len(), 1, "exactly one if-continuation frame minted");
    assert_eq!(prog.if_kont_row_id.len(), 1);
    assert_eq!(
        prog.if_taken,
        vec![(mcfa_frag::Tag("then", 10), mcfa_frag::Tag("if", 1))],
        "the join back through if_kont_row_id recovered the frame's fields correctly"
    );
}

// ---------------------------------------------------------------------------
// The demand-driven `function atomic_eval` and the eager `atomic_eval_plain`
// must compute the same answer set (same expr ref -> value ref mapping),
// confirming `function` is a faithful (if here unnecessary -- see the module
// doc comment) rewrite of the eager version.
// ---------------------------------------------------------------------------

fn atomic_eval_answers(prog: &mcfa_frag::McfaFrag) -> Vec<(mcfa_frag::Tag, mcfa_frag::Tag)> {
    let mut out: Vec<_> = prog
        .atomic_eval_do_id
        .iter()
        .cloned()
        .filter_map(|(key, do_id)| {
            prog.atomic_eval.iter().find(|(id, _v)| *id == do_id).map(|(_id, v)| (key, *v))
        })
        .collect();
    out.sort();
    out
}

#[test]
fn function_atomic_eval_is_a_subset_of_eager_atomic_eval_plain() {
    // The demand-driven `function` version only answers for expr refs that
    // were actually demanded (reached by some `state_e`); the eager
    // `atomic_eval_plain` version computes for every `num_e`/`bool_e`/`lam_e`/
    // `var_e` row unconditionally, reached or not. So `via_function` should
    // be a *subset* of `via_plain`, not necessarily equal to it -- and on
    // `term3()` (the `if` term, where the else-branch's lambda is never
    // reached), it is a *strict* subset: this is the one place in this
    // fragment where "demand-driven" actually prunes work the eager version
    // does needlessly.
    for (ast, expect_strict) in [(term1(), false), (term2(), false), (term3(), true)] {
        let prog = mcfa_frag::run_frag(&ast);
        let via_function: HashSet<_> = atomic_eval_answers(&prog).into_iter().collect();
        let via_plain: HashSet<_> = prog.atomic_eval_plain.iter().cloned().collect();
        assert!(!via_plain.is_empty());
        assert!(
            via_function.is_subset(&via_plain),
            "demand-driven atomic_eval produced an answer the eager version didn't"
        );
        assert_eq!(
            via_function.len() < via_plain.len(),
            expect_strict,
            "expected {}a strict subset for this term (function={:?}, plain={:?})",
            if expect_strict { "" } else { "not " },
            via_function,
            via_plain
        );
    }
}
