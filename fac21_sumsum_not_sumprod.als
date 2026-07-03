// Model 21 -- Why SUM(DISTINCT) needs the semi-join domain, NOT a COUNT-style weight-swap. MORK's
// SumSink sums the DISTINCT values of a column over the join. The tempting shortcut -- reuse the
// COUNT sum-product engine with each fact weighted by its column value -- sums the column WITH
// MULTIPLICITY (once per join match), the FAQ "SumProd" form. That differs from SUM(DISTINCT)
// whenever a value appears in more than one match. So the sound route is the semi-join-reduced
// distinct domain (fac19), summed once each -- this model exhibits the discrepancy the shortcut has.
module fac21_sumsum_not_sumprod

sig Match { xval: one Int } // each join match carries the summed column's value

fun distinctX: set Int { Match.xval }
fun sumDistinct: Int { sum v: distinctX | v }  // SUM(DISTINCT x): each distinct value once
fun sumWithMult: Int { sum m: Match | m.xval }  // weight-swap SumProd: once per match

// The weight-swap disagrees with SUM(DISTINCT) once any value repeats across matches. Expect SAT --
// this is the bug avoided by using the semi-join domain instead of ghd_aggregate with a weight.
pred WeightSwapWrong { sumDistinct != sumWithMult }
run WeightSwapWrong for 4 Match, 5 int

// They agree exactly when every match has a distinct value (no repeats). Expect UNSAT (no
// counterexample): an injective column makes distinct-sum and multiplicity-sum coincide.
pred InjectiveX { all disj m1, m2: Match | m1.xval != m2.xval }
assert InjectiveAgrees { InjectiveX => sumDistinct = sumWithMult }
check InjectiveAgrees for 4 Match, 5 int
