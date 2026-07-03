// Model 8 — Semi-naive == naive fixpoint (the incremental capstone).
//
// MORK's fixpoint (transitive, logic_query, bfc) derives new facts each round.
// Naive: re-derive from ALL facts so far (X . R). Semi-naive: derive only from the
// last round's frontier (Delta . R). Sound ONLY under the closure invariant: the
// non-frontier part is already closed one step. This pins that invariant.
//
// NOTE: Alloy's `.` is left-associative and whitespace-blind, so `s.X . s.R` means
// `((s.X).s).R` (empty!). Compositions MUST be parenthesized: `(s.X).(s.R)`.
module fac8_seminaive_fixpoint

sig Val {}
sig State {
  R:     Val -> Val,     // base relation (edges)
  X:     Val -> Val,     // facts derived so far
  Delta: Val -> Val      // facts added in the last round (frontier)
}

pred inv[s: State] {
  s.Delta in s.X                             // frontier is part of the accumulated facts
  ((s.X - s.Delta).(s.R)) in s.X             // non-frontier part already closed one step
}

fun naiveNew[s: State]: Val -> Val { ((s.X).(s.R)) - s.X }       // re-derive from all of X
fun semiNew[s: State]:  Val -> Val { ((s.Delta).(s.R)) - s.X }   // derive only from the frontier

// SOUND + COMPLETE under the invariant: semi-naive finds exactly the naive new facts.
assert SeminaiveExact { all s: State | inv[s] => naiveNew[s] = semiNew[s] }
check SeminaiveExact for 4 Val, 3 State

// Without the invariant they differ (semi-naive misses facts). Expect SAT counterexample.
assert NeedsInvariant { all s: State | naiveNew[s] = semiNew[s] }
check NeedsInvariant for 4 Val, 3 State

// DIAGNOSTIC: the model CAN exhibit a state where the two differ (not vacuous).
pred FindDiff { some s: State | naiveNew[s] != semiNew[s] }
run FindDiff for 4 Val, 3 State
