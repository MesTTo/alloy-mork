// Model 4 — Incremental self-join delta rule (the fixpoint RECOMPUTE win).
//
// MORK's fixpoint (transitive, logic_query, bfc) recomputes self-joins each step
// over the whole growing space: O(|R'|^2) per step. Semi-naive maintenance costs
// O(|delta|.|R'|): join only the delta. This model pins the EXACT correct delta
// rule for the composition self-join R o R (one reachability step), so wiring it
// cannot silently miss or duplicate tuples -- the logic_query 535s meet-self-join.
module fac4_incremental

sig Val {}
sig Edge { s: one Val, t: one Val }   // a directed edge (s,t)
sig Redge in Edge {}                  // edges currently in R
sig Dedge in Edge {}                  // edges added this step (the delta)
fact DeltaDisjoint { no Redge & Dedge }

// composition on the shared middle value: {(x,z) | (x,y) in A, (y,z) in B}
fun compose[A: set Edge, B: set Edge]: Val -> Val {
  { x, z: Val | some y: Val |
      (some e: A | e.s = x and e.t = y) and (some f: B | f.s = y and f.t = z) }
}

fun Rp: set Edge { Redge + Dedge }               // R' = R union delta
fun Jfull: Val -> Val { compose[Rp, Rp] }        // full recompute R' o R'
fun Jold:  Val -> Val { compose[Redge, Redge] }  // last step's result R o R

// candidate incremental delta rule: dJ = (D o R') union (R o D)
fun dJ_correct: Val -> Val { compose[Dedge, Rp] + compose[Redge, Dedge] }
// a plausible WRONG rule that forgets R o D and D o D: dJ = D o R
fun dJ_wrong: Val -> Val { compose[Dedge, Redge] }

// SOUNDNESS: old result + correct delta == full recompute. Expect UNSAT (holds).
assert IncrementalSound { (Jold + dJ_correct) = Jfull }
check IncrementalSound for 6 Edge, 4 Val

// The wrong rule must FAIL: Alloy should find a counterexample (missed tuples).
assert WrongRuleFails { (Jold + dJ_wrong) = Jfull }
check WrongRuleFails for 6 Edge, 4 Val
