//! Smoke-test crate for the "plusplus" fork of Ascent
//! (<https://github.com/michaelballantyne/ascent>, branch `plusplus`, rev
//! `4f80fa11a2640379b34d43fe2e673e7375c71c71`).
//!
//! This crate exists to let the `plusplus` fork's `ascent` package live
//! side-by-side with the workspace's own newer `ascent` (0.8.0, pulled in
//! transitively through the `scheme-mcfa` path dependency) in one Cargo
//! dependency graph, and to smoke-test two of the fork's extra features:
//!
//! - the `delta` marker on body atoms (see `tests/delta.rs`)
//! - `relation ID` / tuple-ID materialization (see `tests/id_relation.rs`)
//!
//! `scheme-mcfa` is pulled in as a dependency so the experiment modules can
//! reuse its AST / term generators / baseline analyses.

pub mod delta_flat;
pub mod slog_style;
