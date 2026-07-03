// Model 6 — d-representation cover: the SCAN-cost fix, made constructive.
//
// Model 2 forced multiple orders (one canonical order fails on incomparable
// bound-sets). Here: HOW MANY orders, and is each a real total byte-order that
// prefix-serves its assigned rules? Dilworth: the minimum number of orders equals
// the maximum antichain of the bound-set poset.
module fac6_drep_cover

sig Col {}
sig Rule { bound: set Col }
pred comparable[a, b: Rule] { a.bound in b.bound or b.bound in a.bound }

sig Order {
  ord: Col -> Col,        // this order's total byte-order on columns
  serves: set Rule        // the rules assigned to descend under this order
}
pred validTotalOrder[o: Order] {
  no (iden & o.ord)
  o.ord.(o.ord) in o.ord
  all disj a, b: Col | (a->b in o.ord) or (b->a in o.ord)
}
pred prefixServed[o: Order, r: Rule] {          // r's bound cols are a prefix of ord
  all b: r.bound, u: (Col - r.bound) | b->u in o.ord
}
pred validCover {
  all o: Order | validTotalOrder[o] and (all r: o.serves | prefixServed[o, r])
  all r: Rule | some o: Order | r in o.serves     // every rule is covered
}
pred antichain[s: set Rule] { all disj r1, r2: s | not comparable[r1, r2] }

// (a) constructive: a valid cover exists (each order a real byte-order).
run CoverExists { validCover and some Rule } for 4 Col, 5 Rule, 3 Order

// (b) Dilworth lower bound: a 3-antichain CANNOT be covered by 2 orders. Expect UNSAT.
run ThreeAntichainTwoOrders {
  validCover and (some s: set Rule | antichain[s] and #s = 3)
} for 4 Col, 5 Rule, 2 Order

// (c) ... but 3 orders DO suffice for the 3-antichain. Expect SAT.
run ThreeAntichainThreeOrders {
  validCover and (some s: set Rule | antichain[s] and #s = 3)
} for 4 Col, 5 Rule, 3 Order
