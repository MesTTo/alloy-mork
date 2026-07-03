// Model 14 — Generalized hypertree decomposition (GHD) soundness.
//
// The asymptotic frontier BEYOND the WCO join (Adam's roadmap, hypertree-decomposition
// -plan): a cyclic query is decomposed into a tree of small BAGS (each a <=k-relation
// sub-join), evaluated by Yannakakis over the bags in O(N^k + OUT), k = width. fhw <=
// ghw <= hw; triangle ghw=2, fhw=3/2. This checks the CORE safety net the design cites:
// "a wrong decomposition cannot produce a wrong answer" -- join-of-bags == join-of-all
// exactly when every relation is covered by some bag (condition C1).
module fac14_ghd

sig Var {}
sig Val {}
sig Tuple { assign: Var -> one Val }     // a full binding (natural join = intersection)
sig Rel { allowed: set Tuple }           // a relation = the bindings it permits
sig Bag { lam: set Rel }                 // a bag = the relations assigned to it (lambda)

fun bagMat[b: Bag]: set Tuple { { t: Tuple | all r: b.lam | t in r.allowed } }  // join of the bag
fun fullJoin: set Tuple { { t: Tuple | all r: Rel | t in r.allowed } }          // join of ALL relations
fun bagJoin:  set Tuple { { t: Tuple | all b: Bag | t in bagMat[b] } }          // join of the bags

pred cover { all r: Rel | some b: Bag | r in b.lam }   // C1: every relation in some bag

// SOUNDNESS: under the cover condition, decomposing then joining the bags is exact.
assert GhdSound { cover => (bagJoin = fullJoin) }
check GhdSound for 4 Var, 3 Val, 4 Rel, 3 Bag, 5 Tuple

// Without cover, an uncovered relation is dropped -> the join over-produces. Expect SAT.
assert NeedsCover { bagJoin = fullJoin }
check NeedsCover for 4 Var, 3 Val, 4 Rel, 3 Bag, 5 Tuple
