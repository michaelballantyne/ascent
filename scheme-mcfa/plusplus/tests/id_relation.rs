//! Smoke test for the plusplus fork's tuple-ID materialization feature
//! (see `README.MD`, section "Materialization of tuple ID", fetched via
//! `git show origin/plusplus:README.MD` on branch `plusplus`).
//!
//! `relation ID foo(i32);` desugars to a plain `relation foo(i32);` plus a
//! companion `relation foo_id(i32, usize);`. A head clause written as
//! `>?id.foo(x) <-- bar(x);` desugars to `!foo(x) <-- bar(x);` (the `!`
//! forces the row to only materialize when actually newly generated) plus a
//! twin `foo_id(x, id) <-- bar(x);` where `id` is bound to the freshly
//! auto-incremented index of the row within `foo`.

use std::collections::{HashMap, HashSet};

use ascent::ascent;

ascent! {
    struct IdRel;

    relation ID foo(i32);
    relation bar(i32);

    bar(1);
    bar(2);
    bar(3);

    >?id.foo(x) <-- bar(x);
}

#[test]
fn id_relation_smoke_test() {
    let mut prog = IdRel::default();
    prog.run();

    let foo_set: HashSet<i32> = prog.foo.iter().map(|(x,)| *x).collect();
    assert_eq!(foo_set, HashSet::from([1, 2, 3]), "foo should contain exactly the bar facts");

    let mut x_to_id: HashMap<i32, usize> = HashMap::new();
    let mut seen_ids: HashSet<usize> = HashSet::new();
    for (x, id) in prog.foo_id.iter().cloned() {
        assert!(seen_ids.insert(id), "foo_id assigned duplicate id {id} (to x={x})");
        assert!(x_to_id.insert(x, id).is_none(), "foo_id has more than one row for x={x}");
    }

    assert_eq!(x_to_id.len(), 3, "foo_id should have one row per distinct foo tuple");
    assert_eq!(seen_ids, HashSet::from([0usize, 1, 2]), "ids should be a dense 0..3 range");
}
