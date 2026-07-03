// Model 5 — What the COW-staleness oracle must key on (the one novel invariant).
//
// Incremental self-join J = R o R under delta D. COW makes recomputation cheap
// ONLY if we recompute over the small set of subtries whose identity changed.
// Which subtries? A value is "dirty" iff a delta edge touches it. The question:
// is it enough to recompute the join around DIRTY MIDDLE (join-variable) nodes,
// or must we look elsewhere? Getting this wrong silently drops fixpoint tuples.
module fac5_cow_staleness

sig Val {}
sig Edge { s: one Val, t: one Val }
sig Redge in Edge {}
sig Dedge in Edge {}
fact DeltaDisjoint { no Redge & Dedge }

fun Rp: set Edge { Redge + Dedge }
fun dirty: set Val { Dedge.s + Dedge.t }           // values touched by a delta edge

fun compose[A: set Edge, B: set Edge]: Val -> Val {
  { x, z: Val | some y: Val |
      (some e: A | e.s = x and e.t = y) and (some f: B | f.s = y and f.t = z) }
}
fun Jold:  Val -> Val { compose[Redge, Redge] }
fun Jfull: Val -> Val { compose[Rp, Rp] }

// Recompute the join only THROUGH dirty middle nodes (join variable = y).
fun recompute_dirtyMiddle: Val -> Val {
  { x, z: Val | some y: dirty |
      (some e: Rp | e.s = x and e.t = y) and (some f: Rp | f.s = y and f.t = z) }
}
// Wrong key: recompute only where the SOURCE x is dirty (misses R o D, x clean).
fun recompute_dirtySource: Val -> Val {
  { x, z: Val | x in dirty and (some y: Val |
      (some e: Rp | e.s = x and e.t = y) and (some f: Rp | f.s = y and f.t = z)) }
}

// COMPLETE: keying on dirty MIDDLE nodes suffices. Expect UNSAT (holds).
assert DirtyMiddleComplete { (Jold + recompute_dirtyMiddle) = Jfull }
check DirtyMiddleComplete for 6 Edge, 4 Val

// INCOMPLETE: keying on dirty SOURCE misses tuples. Expect SAT (counterexample).
assert DirtySourceComplete { (Jold + recompute_dirtySource) = Jfull }
check DirtySourceComplete for 6 Edge, 4 Val
