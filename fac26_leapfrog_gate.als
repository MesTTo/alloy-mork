/*
 * fac26_leapfrog_gate.als
 *
 * The leapfrog dispatch gate (MORK PR #124): the WCO leapfrog join sits behind
 * an experimental `leapfrog` cargo feature; within the feature a thread-local
 * runtime toggle (MORK_LEAPFROG) can pin it off; and the router only accepts a
 * flat relation-prefixed conjunction. So the routed engine is selected iff
 * feature AND toggle AND shape all hold; every other state takes the stock
 * ProductZipper. The answer set is engine-independent (the branch's byte-
 * identity differentials and the Isabelle TotalRouterSafe proof carry that
 * separately, stated here as the agreement fact), so the gate can only ever
 * choose WHO computes, never WHAT.
 *
 * Gates:
 *   G1 RoutedOnlyWhenAllHold: the leapfrog runs only in the one all-on state.
 *   G2 GateTotal: every gate state selects exactly one engine (no third
 *      behavior, no fall-through).
 *   G3 AnswersGateIndependent: under the agreement fact, the observed answer
 *      set is the same in every gate state -- flipping the feature, the env
 *      toggle, or the query shape never changes results.
 */
module fac26_leapfrog_gate

abstract sig Flag {}
one sig On, Off extends Flag {}

abstract sig Shape {}
one sig Flat, Other extends Shape {}

abstract sig Engine {}
one sig Stock, Leapfrog extends Engine {}

sig Answer {}

// the gate: (feature, toggle, shape) -> engine, exactly as the code selects
one sig Gate { pick: Flag -> Flag -> Shape -> one Engine }
fact GateTable {
  all f, t: Flag, s: Shape |
    Gate.pick[f][t][s] = (f = On and t = On and s = Flat implies Leapfrog else Stock)
}

// each engine's answer set for the query under consideration; the byte-identity
// differentials + TotalRouterSafe establish they agree
one sig Run { answers: Engine -> set Answer }
fact EnginesAgree { Run.answers[Stock] = Run.answers[Leapfrog] }

// G1: the leapfrog is selected only in the single all-on state.
assert RoutedOnlyWhenAllHold {
  all f, t: Flag, s: Shape |
    Gate.pick[f][t][s] = Leapfrog implies (f = On and t = On and s = Flat)
}
check RoutedOnlyWhenAllHold for 4

// G2: the gate is total and deterministic over its whole state space.
assert GateTotal {
  all f, t: Flag, s: Shape | one Gate.pick[f][t][s]
}
check GateTotal for 4

// G3: the observed answers are identical in every gate state.
assert AnswersGateIndependent {
  all f1, t1: Flag, s1: Shape, f2, t2: Flag, s2: Shape |
    Run.answers[Gate.pick[f1][t1][s1]] = Run.answers[Gate.pick[f2][t2][s2]]
}
check AnswersGateIndependent for 4

// non-vacuity: both engines are reachable through the gate.
run BothEnginesReachable {
  some f, t: Flag, s: Shape | Gate.pick[f][t][s] = Leapfrog
  some f, t: Flag, s: Shape | Gate.pick[f][t][s] = Stock
} for 4
