// Model 7 — factorized-match soundness: the EMIT-cost enabler.
//
// The plateau: every join wins until it must EXPAND its output to flat tuples so
// the next rule can match. If instead the output stays factorized (a union of
// products = the trie's shared structure) and the next match runs DIRECTLY on the
// factorized form, the flat output is never materialized. This checks that such a
// factorized match is sound -- and pins the mistake that would silently corrupt it.
module fac7_factorized_match

sig Val {}
sig Product { xs: set Val, ys: set Val }   // one product block: represents xs x ys tuples over (x,y)
one sig Q { qx: one Val }                   // pattern: x = qx, y free

// flat: expand every product, then filter by the pattern x = qx
fun matchFlat: Val -> Val {
  { a, b: Val | a = Q.qx and (some p: Product | a in p.xs and b in p.ys) }
}
// correct factorized match: keep products whose xs contains qx, bind x=qx, keep their ys
fun matchFactorizedCorrect: Val -> Val {
  { a, b: Val | a = Q.qx and (some p: Product | Q.qx in p.xs and b in p.ys) }
}
// WRONG: inside a matching product, forget to restrict x to qx (emit all of p.xs)
fun matchFactorizedWrong: Val -> Val {
  { a, b: Val | some p: Product | Q.qx in p.xs and a in p.xs and b in p.ys }
}

// SOUND: factorized match == flat match. Expect UNSAT (holds).
assert FactorizedMatchSound { matchFactorizedCorrect = matchFlat }
check FactorizedMatchSound for 5 Product, 4 Val

// The wrong pruning must FAIL: Alloy finds a product with an extra x-value. Expect SAT.
assert WrongMatchFails { matchFactorizedWrong = matchFlat }
check WrongMatchFails for 5 Product, 4 Val
