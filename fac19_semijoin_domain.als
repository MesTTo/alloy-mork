// Model 19 -- Semi-join reduction soundness for SUM(DISTINCT x): the routing gate for the SumSink.
//
// MORK's SumSink sums the DISTINCT values of a projected column x over the join output. The
// factorized route sums x's "surviving domain": the x-values that participate in at least one full
// join answer, computed by keeping x free and eliminating every other variable over the EXISTS
// (boolean) semiring -- FAQ's free-variable form, which for the boolean semiring is exactly the
// Yannakakis / Bernstein-Goodman full reducer. This model checks that the free-variable elimination
// equals the join's x-projection (so the distinct values summed are identical), and that a dangling
// tuple (an x with no join partner) is correctly excluded -- the x=40 case in the Rust test.
module fac19_semijoin_domain

sig V {}
sig R { x: one V, y: one V }   // R(x, y)
sig S { yy: one V, z: one V }  // S(y, z), joined on y

// The x-values in the full join output R(x,y) join S(y,z): those with a matching (y,z).
fun joinProjX: set V { { xv: V | some r: R, s: S | (r.x = xv) and (r.y = s.yy) } }

// Free-variable elimination keeping x: eliminate z (S reduced to its y-domain: exists z. S(y,z)),
// then eliminate y (R kept where its y is in that domain). The surviving x-values.
fun reducedSY: set V { { yv: V | some s: S | s.yy = yv } }
fun elimX: set V { { xv: V | some r: R | (r.x = xv) and (r.y in reducedSY) } }

// SOUND: the free-variable elimination equals the join's x-projection, so summing the surviving
// domain sums exactly the distinct x that appear in the output. Expect UNSAT.
assert SemijoinDomainExact { joinProjX = elimX }
check SemijoinDomainExact for 6

// The reduction is not a no-op: a dangling x (present in R but with no join partner) is excluded
// from the summed domain. This is why x=40 (no rel2 partner) drops out. Expect SAT.
pred DanglingExcluded { some xv: V | (some r: R | r.x = xv) and (xv not in joinProjX) }
run DanglingExcluded for 6
