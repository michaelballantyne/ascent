//! Smoke test for the plusplus fork's `delta` marker on body atoms.
//!
//! The fork lets a rule mark exactly one body atom with `delta`, which
//! compiles the rule to a single semi-naive version using that atom's delta
//! as the driver, instead of the usual "one semi-naive rule per dynamic
//! atom" expansion. Using it correctly means manually writing one
//! delta-first rule per dynamic (recursive) atom in the rule -- for
//! transitive closure that means three rules mirroring the fork's own test
//! in `ascent_tests/src/incremental.rs` (branch `plusplus`, function
//! `run_tc_incremental`):
//!
//! ```ignore
//! path(x, y) <-- delta edge(x, y);
//! path(x, z) <-- delta path(x, y), edge(y, z);
//! path(x, z) <-- delta edge(y, z), path(x, y);
//! ```
//!
//! This file builds transitive closure two ways -- the "normal" way and the
//! "delta" way -- over the same deterministically generated graph (chains,
//! a cycle, and cross links) and asserts the resulting `path` sets are
//! identical.

use std::collections::HashSet;

use ascent::ascent;

ascent! {
    struct NormalTC;

    // Facts are fed in through an `extern arguement` (the fork's intentional
    // spelling) rather than assigned to the relation field directly, since
    // that keeps the seeding mechanism identical between the two programs
    // and doesn't depend on the internal storage type ascent picks for a
    // plain `relation`.
    //
    // NB: the argument type here must be an *owned* `Vec`, not `&Vec`. The
    // plusplus codegen forwards extern arguments between its internal
    // dispatch functions with a bare `.clone()` call; for a reference-typed
    // argument like `&Vec<(i32, i32)>`, method resolution picks
    // `Vec::clone` through autoderef (since `Vec<T>: Clone`) instead of the
    // reference's own identity `Clone` impl, silently turning `&Vec<T>`
    // into `Vec<T>` and breaking the internal call with a type mismatch.
    // Declaring the argument as an owned `Vec` sidesteps the bug because
    // `.clone()` then returns the same `Vec<T>` type the call site expects.
    extern arguement Vec<(i32, i32)> edges_arg;

    relation edge_in(i32, i32);
    // `edge` must be a derived/dynamic relation (not a base fact relation)
    // for `delta edge` to make sense in the DeltaTC program below; we keep
    // the same shape here so both programs are structurally comparable.
    relation edge(i32, i32);
    relation path(i32, i32);

    edge_in(x, y) <-- for &(x, y) in edges_arg.iter();
    edge(x, y) <-- edge_in(x, y);

    path(x, y) <-- edge(x, y);
    path(x, z) <-- edge(x, y), path(y, z);
}

ascent! {
    struct DeltaTC;

    extern arguement Vec<(i32, i32)> edges_arg;

    relation edge_in(i32, i32);
    relation edge(i32, i32);
    relation path(i32, i32);

    edge_in(x, y) <-- for &(x, y) in edges_arg.iter();
    edge(x, y) <-- edge_in(x, y);

    path(x, y) <-- delta edge(x, y);
    path(x, z) <-- delta path(x, y), edge(y, z);
    path(x, z) <-- delta edge(y, z), path(x, y);
}

/// Deterministic graph with chains, a cycle, a "random-ish" tangle, and a
/// couple of cross links between the components -- 30 nodes (0..30).
fn make_edges() -> Vec<(i32, i32)> {
    let mut edges = vec![];

    // A plain chain: 0 -> 1 -> ... -> 9
    for i in 0..9 {
        edges.push((i, i + 1));
    }

    // A cycle: 10 -> 11 -> ... -> 19 -> 10
    for i in 10..19 {
        edges.push((i, i + 1));
    }
    edges.push((19, 10));

    // Deterministic "random-ish" edges among nodes 20..29
    for i in 20..30 {
        let target = (i * 7 + 3) % 30;
        edges.push((i, target));
    }

    // Cross links tying the three components together
    edges.push((9, 20));
    edges.push((19, 25));

    edges
}

#[test]
fn delta_marker_matches_normal_semi_naive() {
    let edges = make_edges();

    let mut normal = NormalTC::default();
    normal.run(edges.clone());

    let mut delta = DeltaTC::default();
    delta.run(edges.clone());

    let normal_path: HashSet<(i32, i32)> = normal.path.iter().cloned().collect();
    let delta_path: HashSet<(i32, i32)> = delta.path.iter().cloned().collect();

    assert!(!normal_path.is_empty(), "sanity check: normal TC should derive some paths");
    assert_eq!(
        normal_path, delta_path,
        "delta-style semi-naive transitive closure must match the normal one"
    );
}
