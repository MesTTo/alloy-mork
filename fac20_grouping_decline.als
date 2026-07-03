// Model 20 -- Why the aggregate gate must DECLINE grouping. A grouped aggregate (a pattern variable
// free in the sink template, e.g. (count of $k is $n)) emits one fact PER distinct value of that
// grouping variable; the factorized fast path computes a single scalar and emits one fact. With no
// grouping variable the aggregate is a single total (one fact) and the scalar is exact; with one it
// can emit many. The gate routes iff the template mentions no pattern variable -- exactly this.
module fac20_grouping_decline

sig Val {}                   // values the grouping variable can take
sig Match { gkey: lone Val } // this match's grouping value; `none` for all matches = no grouping variable

fun distinctGroups: set Val { Match.gkey }
// The enumerate sink emits one fact per distinct grouping value, or one total fact if the query has
// no grouping variable at all.
fun enumerateFacts: Int { (no Match.gkey) => 1 else #distinctGroups }
fun scalarFacts: Int { 1 } // the factorized fast path emits a single total fact

pred HasGroupingVar { some Match.gkey }

// SOUND to route when there is no grouping variable: exactly one total fact matches the scalar.
// Expect UNSAT (no counterexample) -- the case the gate routes.
assert NoGroupingIsScalar { (some Match and not HasGroupingVar) => enumerateFacts = scalarFacts }
check NoGroupingIsScalar for 5

// UNSOUND to route when a grouping variable yields more than one group: the enumerate sink emits
// more facts than the single scalar. Expect SAT -- the case the gate must reject.
pred GroupingEmitsMany { HasGroupingVar and enumerateFacts > scalarFacts }
run GroupingEmitsMany for 5
