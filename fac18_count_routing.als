// Model 18 — CountSink routing soundness: the missing link between the factorized count and the sink.
//
// fac17 proved the factorized aggregate equals the enumerated MATCH count (Sum_y |R_y|*|S_y|).
// But the CountSink does not count matches -- it counts DISTINCT OUTPUTS: it instantiates a
// template/projection per match, dedups them in a PathMap, and reports the number of distinct
// output tuples. So routing the sink to the factorized engine is sound only when distinct-output
// count == match count.
//
// A "match" is a distinct assignment to all query variables (relations are sets; the join emits
// each satisfying assignment once). The sink's output keeps only the projected variables `proj`;
// two matches collapse to the same output iff they agree on every projected variable. Therefore
// distinct-output == match count IFF the projection is INJECTIVE on matches, which holds exactly
// when `proj` covers all variables. Drop a join variable and the sink undercounts -- unsound.
module fac18_count_routing

sig Value {}
sig Var {}
one sig P { proj: set Var }          // the sink's projection: which variables it keeps

sig Output {}
sig Assign {                          // a match: a full assignment of every variable to a value
  val: Var -> one Value,
  out: one Output                     // the sink's instantiated, deduped output tuple
}

// Matches are distinct as valuations: no two matches assign identical values to every variable
// (they would be the same match). This is what "the join emits each assignment once" means.
fact DistinctMatches {
  all a, b: Assign | (all v: Var | a.val[v] = b.val[v]) => a = b
}

// The output is the projection quotient: two matches share an output iff they agree on every kept
// (projected) variable. This is exactly what the CountSink's dedup-by-instantiated-template does.
fact OutputIsProjectionQuotient {
  all a, b: Assign | (a.out = b.out) <=> (all v: P.proj | a.val[v] = b.val[v])
}
fact NoOrphanOutputs { Output = Assign.out }

fun sinkCount: Int { #Output }        // what the CountSink reports: distinct outputs
fun matchCount: Int { #Assign }       // what the factorized engine reports: satisfying assignments

pred FullProjection { P.proj = Var }  // the routing gate: the projection keeps every variable

// SOUND: under a full projection the sink's distinct-output count equals the factorized match
// count, so routing is safe. Expect UNSAT (no counterexample within scope).
assert RoutingSoundUnderFullProjection { FullProjection => sinkCount = matchCount }
check RoutingSoundUnderFullProjection for 5

// GAP: drop a variable from the projection and the sink can strictly undercount the matches --
// this is precisely the case the gate must reject and fall back to enumerate. Expect SAT.
pred DropsAVariable { some (Var - P.proj) }
run ProjectionDropUndercounts { DropsAVariable and sinkCount < matchCount } for 5
