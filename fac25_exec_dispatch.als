/*
 * fac25_exec_dispatch.als
 *
 * The exec special-form dispatch contract (Space::interpret, kernel/src/space.rs):
 * an `(exec <loc> <patterns> <templates>)` is routed iff the pattern functor is
 * `,` or `I` and the template functor is `,` or `O`; the four valid combinations
 * map to the four transform kernels via two independent io flags (a source is in
 * play iff the pattern functor is `I`; sinks are in play iff the template functor
 * is `O`). metta_calculus removes an exec before interpreting, so a rejected exec
 * is consumed without effect. Companion behavior tests:
 * kernel/tests/exec_special_forms.rs (MORK PR #109).
 *
 * Gates:
 *   G1 DispatchTotalOnValid: every valid functor combination is routed, and to
 *      exactly one kernel (no valid shape falls through to the error arm).
 *   G2 InvalidRejected: any other functor combination is rejected (never routed).
 *   G3 FlagsFaithful: the routed kernel's io flags mirror the functors exactly --
 *      sources iff `I`, sinks iff `O` -- so `,`/`,` never touches the IO machinery
 *      and `I`/`O` always engages both.
 */
module fac25_exec_dispatch

abstract sig PatFunctor {}
one sig PComma, PI, POther extends PatFunctor {}

abstract sig TplFunctor {}
one sig TComma, TO, TOther extends TplFunctor {}

abstract sig Kernel { usesSources: one Bool, usesSinks: one Bool }
one sig KPlain, KIn, KOut, KInOut extends Kernel {}
abstract sig Bool {}
one sig True, False extends Bool {}

fact KernelFlags {
  KPlain.usesSources = False and KPlain.usesSinks = False
  KIn.usesSources   = True  and KIn.usesSinks   = False
  KOut.usesSources  = False and KOut.usesSinks  = True
  KInOut.usesSources = True and KInOut.usesSinks = True
}

// the dispatch table, exactly as the match in interpret routes it
one sig Dispatch { route: PatFunctor -> TplFunctor -> lone Kernel }
fact DispatchTable {
  Dispatch.route[PComma][TComma] = KPlain
  Dispatch.route[PI][TComma]     = KIn
  Dispatch.route[PComma][TO]     = KOut
  Dispatch.route[PI][TO]         = KInOut
  no Dispatch.route[POther]
  all p: PatFunctor | no Dispatch.route[p][TOther]
}

pred valid[p: PatFunctor, t: TplFunctor] { p in PComma + PI and t in TComma + TO }

// G1: every valid combination routes to exactly one kernel.
assert DispatchTotalOnValid {
  all p: PatFunctor, t: TplFunctor | valid[p, t] implies one Dispatch.route[p][t]
}
check DispatchTotalOnValid for 4

// G2: everything else is rejected.
assert InvalidRejected {
  all p: PatFunctor, t: TplFunctor | not valid[p, t] implies no Dispatch.route[p][t]
}
check InvalidRejected for 4

// G3: the io flags mirror the functors -- sources iff I, sinks iff O.
assert FlagsFaithful {
  all p: PatFunctor, t: TplFunctor | valid[p, t] implies {
    Dispatch.route[p][t].usesSources = True iff p = PI
    Dispatch.route[p][t].usesSinks   = True iff t = TO
  }
}
check FlagsFaithful for 4

// non-vacuity: all four kernels are reachable through the table.
run AllKernelsReachable {
  all k: Kernel | some p: PatFunctor, t: TplFunctor | Dispatch.route[p][t] = k
} for 4
