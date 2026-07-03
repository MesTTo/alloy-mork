// Model 2 — The fixpoint ORDER-CONFLICT (the core of the discovery).
//
// MORK stores every atom in ONE canonical column order (the s-expression byte
// order). A rule is "factorized" on the trie (frontier-scaling, no flat scan)
// iff its bound columns form a PREFIX of the stored order: you can descend/seek
// the trie only while every column before your first free column is bound.
//
// Question: across a fixpoint of rules, can a single canonical order be a common
// prefix-order for ALL rules, or is a flat scan forced?
module fac2_fixpoint

sig Col {}
sig Rule { bound: set Col }         // columns this rule seeks / joins on

// THE single canonical order, chosen per instance: a strict total order on Col.
one sig O { ord: Col -> Col }
pred validOrder {
  no (iden & O.ord)                                          // irreflexive
  O.ord.(O.ord) in O.ord                                     // transitive
  all disj a, b: Col | (a->b in O.ord) or (b->a in O.ord)    // total
}

// rule r is prefix-served: every bound col precedes every unbound col in ord
pred prefixServed[r: Rule] {
  all b: r.bound, u: (Col - r.bound) | b->u in O.ord
}
pred ordPrefixesAll { all r: Rule | prefixServed[r] }

// non-chain ruleset: two rules with incomparable bound-sets (neither contains the other)
pred notChain { some r1, r2: Rule | (r1.bound !in r2.bound) and (r2.bound !in r1.bound) }

// NECESSITY. If UNSAT: a non-chain ruleset has NO single order serving all rules
// => at least one rule is forced to flat-scan. This is the theorem.
run Conflict { validOrder and notChain and ordPrefixesAll } for 5 Col, 5 Rule

// SUFFICIENCY (demo). If SAT: a chain ruleset DOES admit a serving order.
run ChainWorks {
  validOrder and (not notChain) and ordPrefixesAll
  and (some r: Rule | some r.bound and r.bound != Col)
} for 5 Col, 5 Rule

// Minimal conflict witness: two rules binding two different single columns.
run MinConflict { notChain } for exactly 2 Col, exactly 2 Rule
