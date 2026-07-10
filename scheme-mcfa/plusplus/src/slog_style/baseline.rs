//! Baseline: the README's own "Materialization of tuple ID" +
//! "Defunctionalization" example (edge / path / `Tag` / `path_length`),
//! adapted only enough to be self-checking (no externally-supplied "input"
//! demand key to guess at — instead we demand `path_length` for *every*
//! edge/path that exists, and check the result against an independent
//! Rust-side recomputation of path depth).
//!
//! This exists purely to establish that `relation ID`, `>?id.`, `.id`, and
//! `function`/`%` all still work together, end to end, under this fork
//! revision, before attempting anything m-CFA-shaped with them. The
//! rule shapes are copied as closely as possible from the fork's own
//! `ascent_tests/src/provenance.rs::Length` / `ascent_macro/src/tests.rs::test_function`
//! (the only places *in the fork's own test suite* that exercise `function`),
//! since those are known to have compiled for the fork's author, whereas the
//! README prose turns out to disagree with them in one respect (see below).

use std::collections::HashMap;

use ascent::ascent;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tag(pub &'static str, pub usize);

ascent! {
    pub struct PathLength;

    relation edge_raw(i32, i32);
    relation ID edge(i32, i32);
    relation ID path(i32, Tag);

    // normal transitive closure, materializing an id for every edge/path row
    >?id.edge(x, y) <-- edge_raw(x, y);

    >?new_id.path(x, nest_id.clone()) <--
        edge(x, y).eid,
        let nest_id = Tag("edge", *eid);

    >?new_id.path(x, nest_id.clone()) <--
        edge(x, y),
        path(y, _).pid,
        let nest_id = Tag("path", *pid);

    function path_length(Tag) -> usize;

    // Demand a length for every edge and every path that actually exists,
    // rather than threading in an externally-chosen "input" key (avoids
    // hard-coding a materialized id we'd have to guess).
    %path_length(Tag("edge", *eid)) -> ? <-- edge(_x, _y).eid;
    %path_length(Tag("path", *pid)) -> ? <-- path(_x, _y).pid;

    // base case: an edge's path has length 1
    %path_length(?Tag("edge", _eid)) -> ret_val
        <--
        let ret_val = 1;

    // recursive case: a path's length is 1 + the length of what it nests.
    // NB: the fork's own working example spells "use this already-bound
    // pattern variable as the id filter" as `.*pid` (a *dereferenced*
    // expression), not the README's bare `.pid` — the id-suffix slot parses
    // a full `syn::Expr`, and `?`-pattern destructuring binds by reference,
    // so reusing `pid` here without the `*` either fails to typecheck or
    // (worse) silently parses as a *fresh* binding that shadows the pattern
    // variable instead of filtering by it.
    %path_length(?Tag("path", pid)) -> ret_val
        <--
        path(_x, res).*pid,
        %path_length(res) -> rest_length,
        let ret_val = rest_length + 1;
}

/// Runs the [`PathLength`] program on `edges` and returns:
/// - the program itself (so callers/tests can inspect any relation), and
/// - an independently Rust-side-recomputed `Tag -> depth` map, walking
///   `edge_id`/`path_id`/`path_length_do_id` by hand, for cross-checking
///   `path_length`'s answers without hard-coding expected depths.
pub fn run(edges: Vec<(i32, i32)>) -> PathLength {
    let mut prog = PathLength::default();
    prog.edge_raw = edges;
    prog.run();
    prog
}

/// Rust-side recomputation of "depth" for every materialized `path`/`edge`
/// row, by walking the nesting `Tag` chain (edge = depth 1; path nesting
/// tag T = 1 + depth(T)). Used to check `path_length`'s answers against a
/// second, independent implementation instead of hard-coded numbers.
pub fn expected_depths(prog: &PathLength) -> HashMap<Tag, usize> {
    // path_id : (i32, Tag, usize) -- (x, nest_tag, this path row's own id)
    // we want, for every path row, the Tag that *refers to it*: Tag("path", id)
    let mut by_tag_depth: HashMap<Tag, usize> = HashMap::new();
    for (_x, _y, eid) in prog.edge_id.iter().cloned() {
        by_tag_depth.insert(Tag("edge", eid), 1);
    }
    // path rows may reference other path rows not yet resolved; fixpoint by hand.
    let path_rows: Vec<(i32, Tag, usize)> = prog.path_id.iter().cloned().collect();
    let mut remaining = path_rows;
    let mut progress = true;
    while progress && !remaining.is_empty() {
        progress = false;
        remaining.retain(|(_x, nest_tag, this_id)| {
            if let Some(d) = by_tag_depth.get(nest_tag).cloned() {
                by_tag_depth.insert(Tag("path", *this_id), d + 1);
                progress = true;
                false
            } else {
                true
            }
        });
    }
    assert!(remaining.is_empty(), "path Tag chain did not resolve (cycle?)");
    by_tag_depth
}

/// Reads off `path_length`'s answer for `tag`, following the two-hop
/// `path_length_do_id -> path_length` lookup the `function` sugar actually
/// generates (see the module doc comment in `slog_style.rs`: the answer
/// relation is keyed by the *demand's* materialized id, not by `Tag`
/// itself).
pub fn path_length_of(prog: &PathLength, tag: &Tag) -> Option<usize> {
    let do_id = prog.path_length_do_id.iter().find(|(t, _id)| t == tag).map(|(_t, id)| *id)?;
    prog.path_length.iter().find(|(id, _v)| *id == do_id).map(|(_id, v)| *v)
}
