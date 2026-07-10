//! Experiment 3: incremental m-CFA via the plusplus fork's re-runnable
//! fixpoint (`run_with_init_flag(false)`, exposed runtime_total/new state,
//! phantom relations) — feed the EDB in chunks and continue the fixpoint
//! instead of recomputing from scratch.
//!
//! ## What actually works, and why
//!
//! The obvious-looking API for this is `run_with_init_flag(false)` plus
//! writing directly into `prog.runtime_total.<rel>_indices_*`, mirroring the
//! fork's own `ascent_tests/src/incremental.rs::run_tc_incremental` (which
//! uses a `phantom` BYODS relation and does
//! `tc.runtime_total.edge_incremental_indices_none.0 = ...`). That relies on
//! `ascent-byods-rels`, which is **not** a dependency of this crate and which
//! we are not allowed to add (see the crate-level constraints in this repo).
//! So this module uses a different, simpler mechanism that needs nothing
//! beyond what `ascent!` already generates for ordinary relations, verified
//! against the fork's own codegen and empirically against a hand-written
//! probe program before being applied here:
//!
//! - `ascent_macro/src/codegen/mir2rust.rs` shows that
//!   `run_with_init_flag(init_flag)` differs from a plain `run()` (which is
//!   just `run_with_init_flag(true)`) in exactly one respect: whether
//!   `update_indices_priv()` is called. That function (see
//!   `ascent_macro/src/codegen/update_indices.rs`) is the *only* code that
//!   ever reads a relation's plain `Vec` field (`self.<rel>`) into its
//!   `runtime_total` index — it does `for tuple in self.<rel>.iter() { ...
//!   insert into runtime_total ... }`. So with `init_flag = false`,
//!   reassigning `prog.<edb_relation> = new_facts` is silently ignored: the
//!   engine never looks at the plain field again, and only a direct
//!   `runtime_total`/`runtime_delta` write (the phantom-relation route)
//!   would be observed. We confirmed this with a minimal probe program: an
//!   `init_flag = false` continuation after reassigning a plain EDB `Vec`
//!   field leaves every derived relation byte-for-byte unchanged.
//!
//! - With `init_flag = true` (i.e. plain `run()`), `update_indices_priv()`
//!   *does* run, and it is additive: it only inserts whatever is currently
//!   in `self.<rel>` into `runtime_total`, which is never cleared between
//!   `run()` calls for ordinary (non-`extern`) relations. So the injection
//!   mechanism this module uses is: **reassign each EDB relation's plain
//!   `Vec` field to hold *only the new chunk's* tuples** (not the
//!   cumulative history) and call plain `run()`. The already-known facts
//!   stay correctly indexed in `runtime_total` (nothing is re-scanned for
//!   them, so no duplicate index entries), and the new tuples get folded in.
//!
//! - Separately, `ascent_macro/src/codegen/scc.rs` shows that at the start
//!   of *every* `run()`/`run_with_init_flag()` call, for every relation that
//!   is recursively/dynamically derived within a looping SCC (`state_e`,
//!   `state_a`, `stored_val`, `stored_kont`, `peek_ctx`, `copy_ctx`, plus the
//!   smaller `freevar`/`value_form` SCC), the *entire* current
//!   `runtime_total` content for that relation is unconditionally moved into
//!   `runtime_delta` (`move_total_to_delta`, a.k.a. `scc_pre`), with `total`
//!   reset to empty — this happens regardless of `init_flag`. This looks
//!   alarming (it seems to force a full "replay" of everything ever
//!   derived), but the probe showed it is exactly what makes continuation
//!   *correct* for delta_flat.rs-style two-dynamic-atom rules: on the first
//!   iteration of the replay only the single-dynamic-atom rules (where the
//!   other side is a still-fully-visible static/EDB relation) can fire, but
//!   whatever they derive becomes a genuinely new `delta` for the next
//!   iteration, at which point `total` has been restored (via the ordinary
//!   end-of-iteration `delta -> total` merge) and the paired `(a)`/`(b)`
//!   `delta`-marked rule variants that delta_flat.rs already has for every
//!   two-dynamic-atom rule pick the derivation up correctly. We verified
//!   this on a small 2-hop chase program (`reach`/`via`, mirroring
//!   McfaDelta's state_e/peek_ctx-style pairing) injecting a brand new EDB
//!   edge fact after an initial run, and the final result was set-identical
//!   to a batch run over all the facts at once.
//!
//! - The `move_total_to_delta` replay is *not* free, though: because it
//!   moves the *entire* accumulated `total` into `delta` every single call,
//!   the cost of any continuation (however tiny the injected fact set)
//!   scales with the size of the analysis accumulated *so far*, not with the
//!   size of the injection. In a scaling probe (a long `reach`/`via` chain),
//!   continuing with exactly one new tail edge after loading N-1 cost
//!   roughly linearly more time as N grew (about 2.9ms at N=20000, 4.9ms at
//!   N=40000), even though the actual new work was a single edge. See the
//!   timing demo below for the same effect on real m-CFA terms.
//!
//! - Derived (non-EDB) relations' plain `Vec` fields are *not* cleared
//!   between chunks by this module. `update_indices_priv()` would then
//!   re-scan their accumulated content into `runtime_total` too, which risks
//!   duplicate index entries; whether or not that happens, the head-rule
//!   codegen re-derives already-known facts during the SCC replay described
//!   above and could in principle append them to the plain `Vec` fields
//!   again (duplicate *content*, not just index bloat) -- hence this
//!   module's use of `HashSet` comparison rather than `Vec` equality in the
//!   cross-check. (Empirically, in the small probe program plain-`Vec`
//!   duplicates did not actually appear across several chunks -- Ascent's
//!   per-relation full-index dedup absorbed the repeats -- but we make no
//!   assumption that this holds for the larger McfaDelta rule set, so the
//!   cross-check compares as sets regardless, per the task's instructions.)

use std::time::{Duration, Instant};

use scheme_mcfa::edb::Facts;
use scheme_mcfa::Ast;

use crate::delta_flat::{load_facts, McfaDelta};

/// Round-robin-split `v` into `n_chunks` (roughly) equal slices, in a
/// deterministic, index-interleaved fashion: element `i` goes to chunk `i %
/// n_chunks`. This keeps a single-element relation (like `top_exp`, which
/// always has exactly one tuple) in chunk 0, satisfying the "top_exp arrives
/// in the first chunk" requirement without any special-casing.
fn split_round_robin<T>(v: Vec<T>, n_chunks: usize) -> Vec<Vec<T>> {
   assert!(n_chunks >= 1);
   let mut chunks: Vec<Vec<T>> = (0..n_chunks).map(|_| Vec::new()).collect();
   for (i, item) in v.into_iter().enumerate() {
      chunks[i % n_chunks].push(item);
   }
   chunks
}

/// Split one [`Facts`] into `n_chunks` pieces, one EDB relation at a time
/// (via [`split_round_robin`]).
fn split_facts(facts: Facts, n_chunks: usize) -> Vec<Facts> {
   let Facts {
      top_exp,
      lambda,
      lambda_arg_list,
      prim,
      prim_call,
      call,
      call_arg_list,
      var,
      num,
      boolean,
      quotation,
      if_,
      setb,
      callcc,
      let_,
      let_list,
   } = facts;

   let mut top_exp = split_round_robin(top_exp, n_chunks);
   let mut lambda = split_round_robin(lambda, n_chunks);
   let mut lambda_arg_list = split_round_robin(lambda_arg_list, n_chunks);
   let mut prim = split_round_robin(prim, n_chunks);
   let mut prim_call = split_round_robin(prim_call, n_chunks);
   let mut call = split_round_robin(call, n_chunks);
   let mut call_arg_list = split_round_robin(call_arg_list, n_chunks);
   let mut var = split_round_robin(var, n_chunks);
   let mut num = split_round_robin(num, n_chunks);
   let mut boolean = split_round_robin(boolean, n_chunks);
   let mut quotation = split_round_robin(quotation, n_chunks);
   let mut if_ = split_round_robin(if_, n_chunks);
   let mut setb = split_round_robin(setb, n_chunks);
   let mut callcc = split_round_robin(callcc, n_chunks);
   let mut let_ = split_round_robin(let_, n_chunks);
   let mut let_list = split_round_robin(let_list, n_chunks);

   let mut out = Vec::with_capacity(n_chunks);
   for i in 0..n_chunks {
      out.push(Facts {
         top_exp: std::mem::take(&mut top_exp[i]),
         lambda: std::mem::take(&mut lambda[i]),
         lambda_arg_list: std::mem::take(&mut lambda_arg_list[i]),
         prim: std::mem::take(&mut prim[i]),
         prim_call: std::mem::take(&mut prim_call[i]),
         call: std::mem::take(&mut call[i]),
         call_arg_list: std::mem::take(&mut call_arg_list[i]),
         var: std::mem::take(&mut var[i]),
         num: std::mem::take(&mut num[i]),
         boolean: std::mem::take(&mut boolean[i]),
         quotation: std::mem::take(&mut quotation[i]),
         if_: std::mem::take(&mut if_[i]),
         setb: std::mem::take(&mut setb[i]),
         callcc: std::mem::take(&mut callcc[i]),
         let_: std::mem::take(&mut let_[i]),
         let_list: std::mem::take(&mut let_list[i]),
      });
   }
   out
}

/// Concatenate `b`'s tuples onto `a`, relation by relation.
#[cfg(test)]
fn merge_facts(a: &mut Facts, b: Facts) {
   a.top_exp.extend(b.top_exp);
   a.lambda.extend(b.lambda);
   a.lambda_arg_list.extend(b.lambda_arg_list);
   a.prim.extend(b.prim);
   a.prim_call.extend(b.prim_call);
   a.call.extend(b.call);
   a.call_arg_list.extend(b.call_arg_list);
   a.var.extend(b.var);
   a.num.extend(b.num);
   a.boolean.extend(b.boolean);
   a.quotation.extend(b.quotation);
   a.if_.extend(b.if_);
   a.setb.extend(b.setb);
   a.callcc.extend(b.callcc);
   a.let_.extend(b.let_);
   a.let_list.extend(b.let_list);
}

/// Reassign every EDB relation field of `prog` to hold *only* `chunk`'s
/// tuples (not the cumulative history -- see the module doc for why that
/// matters) and continue the fixpoint with a plain `run()` (`init_flag =
/// true`).
fn inject_chunk_and_continue(prog: &mut McfaDelta, chunk: Facts) {
   prog.top_exp = chunk.top_exp;
   prog.lambda = chunk.lambda;
   prog.lambda_arg_list = chunk.lambda_arg_list;
   prog.prim = chunk.prim;
   prog.prim_call = chunk.prim_call;
   prog.call = chunk.call;
   prog.call_arg_list = chunk.call_arg_list;
   prog.var = chunk.var;
   prog.num = chunk.num;
   prog.boolean = chunk.boolean;
   prog.quotation = chunk.quotation;
   prog.if_ = chunk.if_;
   prog.setb = chunk.setb;
   prog.callcc = chunk.callcc;
   prog.let_ = chunk.let_;
   prog.let_list = chunk.let_list;
   prog.run();
}

/// Result of [`analyze_incremental`]: the final, fully-converged program
/// (content-equivalent to a batch [`scheme_mcfa::analyze`] run — see
/// `tests/incremental_check.rs`), plus the wall-clock time of each chunk's
/// `run()` call (`phase_times[0]` is the initial load-and-run, the rest are
/// continuations).
pub struct IncrementalRun {
   pub prog: McfaDelta,
   pub phase_times: Vec<Duration>,
}

/// Split `ast`'s facts into `n_chunks` deterministically-interleaved pieces
/// (see [`split_round_robin`]; `top_exp` always lands in chunk 0), load the
/// first chunk and run it to a fixpoint, then for each subsequent chunk
/// inject its facts and continue the *same* fixpoint (rather than
/// recomputing from scratch) via [`inject_chunk_and_continue`].
///
/// Because m-CFA is monotone Datalog, the chunk boundaries are semantically
/// invisible: the final result must equal (as sets, per relation) a single
/// batch run over all the facts at once. `tests/incremental_check.rs`
/// verifies this against `scheme_mcfa::analyze`.
pub fn analyze_incremental(ast: &Ast, n_chunks: usize) -> IncrementalRun {
   assert!(n_chunks >= 1, "analyze_incremental: n_chunks must be >= 1");
   let facts = Facts::from_ast(ast);
   let mut chunks = split_facts(facts, n_chunks).into_iter();

   let first = chunks.next().expect("n_chunks >= 1");
   let t0 = Instant::now();
   let mut prog = load_facts(first);
   prog.run();
   let mut phase_times = vec![t0.elapsed()];

   assert!(
      !prog.state_e.is_empty(),
      "analyze_incremental: state_e is empty after loading chunk 0 -- top_exp did not \
       land in the first chunk"
   );

   for chunk in chunks {
      let t = Instant::now();
      inject_chunk_and_continue(&mut prog, chunk);
      phase_times.push(t.elapsed());
   }

   IncrementalRun { prog, phase_times }
}

/// Two-phase variant for measuring "small edit, fast re-analysis": splits
/// `ast`'s facts into `last_chunk_fraction` deterministically-interleaved
/// round-robin buckets (same split as [`analyze_incremental`]), then
/// *merges all but the last bucket* into a single first phase and keeps only
/// the final bucket as a separate, tiny continuation. This measures a
/// genuinely small injected fact set (about `1/last_chunk_fraction` of the
/// program) without paying the O(`last_chunk_fraction`) cost of actually
/// making that many separate `run()` calls (each of which pays the
/// `move_total_to_delta` replay cost described in the module doc -- see
/// `incremental_timing_demo` for why doing this with `analyze_incremental`
/// and a large chunk count is impractically slow).
#[cfg(test)]
fn analyze_incremental_tiny_last_chunk(ast: &Ast, last_chunk_fraction: usize) -> IncrementalRun {
   assert!(last_chunk_fraction >= 2, "need at least 2 buckets to split off a last one");
   let facts = Facts::from_ast(ast);
   let mut buckets = split_facts(facts, last_chunk_fraction);
   let last = buckets.pop().expect("last_chunk_fraction >= 2");
   let mut first = buckets.remove(0);
   for b in buckets {
      merge_facts(&mut first, b);
   }

   let t0 = Instant::now();
   let mut prog = load_facts(first);
   prog.run();
   let mut phase_times = vec![t0.elapsed()];
   assert!(!prog.state_e.is_empty(), "analyze_incremental_tiny_last_chunk: state_e empty after phase 0");

   let t1 = Instant::now();
   inject_chunk_and_continue(&mut prog, last);
   phase_times.push(t1.elapsed());

   IncrementalRun { prog, phase_times }
}

#[cfg(test)]
mod timing_demo {
   use std::time::Instant;

   use scheme_mcfa::church_term;

   use super::{analyze_incremental, analyze_incremental_tiny_last_chunk};
   use crate::delta_flat;

   /// Not a correctness test (see `tests/incremental_check.rs` for that) --
   /// prints timing numbers demonstrating that (a) the incremental path's
   /// total work is comparable to one batch run, and (b) the more
   /// interesting number: continuing the fixpoint with a *tiny* last chunk
   /// still costs roughly proportional to the size of the analysis
   /// accumulated *so far* (see the module doc's discussion of
   /// `move_total_to_delta` / `scc_pre`), not to the size of the injected
   /// facts -- i.e. this is not a free "small edit -> instant re-analysis"
   /// in the way one might hope for.
   ///
   /// Two batch baselines are printed: `scheme_mcfa::analyze` (the
   /// *faithful* port, `Mcfa`, default semi-naive expansion) and
   /// `delta_flat::analyze` (`McfaDelta`, the same manually delta-first
   /// rules `analyze_incremental` reuses, run once with all facts loaded
   /// upfront). The `McfaDelta` batch number is the fair apples-to-apples
   /// comparison for "is continuing the fixpoint cheaper than one batch run
   /// of the *same* rule set" -- comparing against `Mcfa` alone would
   /// conflate genuine incrementality savings with the unrelated
   /// delta-first-rule-structure speedup that `McfaDelta` already has over
   /// `Mcfa` even with no incrementality at all.
   ///
   /// Run with:
   ///   cargo test -p scheme-mcfa-plusplus --release incremental_timing_demo -- --nocapture
   #[test]
   fn incremental_timing_demo() {
      for n in [40usize, 60] {
         let ast = church_term(n);

         let t0 = Instant::now();
         let batch = scheme_mcfa::analyze(&ast);
         let batch_time = t0.elapsed();

         let t0d = Instant::now();
         let batch_delta = delta_flat::analyze(&ast);
         let batch_delta_time = t0d.elapsed();

         let n_chunks = 4;
         let run = analyze_incremental(&ast, n_chunks);
         let incremental_total: std::time::Duration = run.phase_times.iter().sum();

         println!(
            "church_term({n}): batch(Mcfa) = {:?}, batch(McfaDelta) = {:?}, \
             incremental(McfaDelta, n_chunks={n_chunks}) total = {:?}, per-chunk = {:?}, \
             state_e Mcfa/McfaDelta-batch/McfaDelta-incremental = {}/{}/{}",
            batch_time,
            batch_delta_time,
            incremental_total,
            run.phase_times,
            batch.state_e.len(),
            batch_delta.state_e.len(),
            run.prog.state_e.len(),
         );

         // The "small program edit, fast re-analysis" scenario: the last
         // chunk is a handful of facts (about 1/40th of the program), fed
         // in as a single continuation after everything else has already
         // reached its own fixpoint.
         let last_chunk_fraction = 40;
         let facts_len = scheme_mcfa::edb::Facts::from_ast(&ast).len();
         let run_tiny = analyze_incremental_tiny_last_chunk(&ast, last_chunk_fraction);
         let last = run_tiny.phase_times[1];
         let total_tiny: std::time::Duration = run_tiny.phase_times.iter().sum();
         println!(
            "church_term({n}): tiny-last-chunk (~{} of {facts_len} facts in the last chunk): \
             batch(Mcfa) = {:?}, batch(McfaDelta) = {:?}, phase0 (bulk load) = {:?}, \
             LAST chunk continuation alone = {:?}, total = {:?}",
            facts_len / last_chunk_fraction,
            batch_time,
            batch_delta_time,
            run_tiny.phase_times[0],
            last,
            total_tiny,
         );
      }
   }
}
