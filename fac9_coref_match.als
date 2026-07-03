// Model 9 — Coreferential matching (the matcher core).
//
// MORK's coreferential_transition (wiki, Data-in-MORK) handles the same De Bruijn
// variable appearing more than once: all occurrences must unify to equal subterms.
// Pattern ($x $y $x): positions 0 and 2 are the SAME variable, position 1 is free.
// This models that coreference is a real restriction and that ignoring it is unsound.
module fac9_coref_match

sig Val {}
sig Tuple { p0: one Val, p1: one Val, p2: one Val }   // a data triple

fun matchCoref: set Tuple { { t: Tuple | t.p0 = t.p2 } }   // coref: pos0 and pos2 must be equal
fun matchNaive: set Tuple { Tuple }                        // ignores coref (2nd $x treated as fresh)

// Coreference correctly excludes tuples whose coreferential positions differ. Expect UNSAT.
assert CorefExcludesUnequal { all t: Tuple | (t.p0 != t.p2) => (t not in matchCoref) }
check CorefExcludesUnequal for 4 Tuple, 3 Val

// A matcher that ignores coreference over-accepts (unsound). Expect SAT counterexample.
assert NaiveUnsound { matchNaive = matchCoref }
check NaiveUnsound for 4 Tuple, 3 Val
