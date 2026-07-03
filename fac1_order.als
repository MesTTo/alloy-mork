// Model 1 — Trie factorization is ORDER-DEPENDENT.
//
// The factorized-across-the-fixpoint question rests on one fact: a relation
// stored as a left-to-right byte trie shares prefixes only for the column order
// it is stored in. MORK stores every atom in ONE canonical order. If the number
// of internal (prefix) nodes can differ between orders, some rule reads it flat.
module fac1_order

sig Val {}
sig Tuple { c0: one Val, c1: one Val, c2: one Val }

// distinct level-2 prefixes for order [c0,c1,..] vs [c0,c2,..]
fun prefAB: Val -> Val { { v, w: Val | some t: Tuple | t.c0 = v and t.c1 = w } }
fun prefAC: Val -> Val { { v, w: Val | some t: Tuple | t.c0 = v and t.c2 = w } }

fun rootN: Int { #(Tuple.c0) }               // root layer, common to both orders
fun sizeABC: Int { plus[rootN, #prefAB] }    // internal nodes, order [c0,c1,c2]
fun sizeACB: Int { plus[rootN, #prefAC] }    // internal nodes, order [c0,c2,c1]

// Claim under test: trie size is the same whichever column is second.
assert OrderIndependent { sizeABC = sizeACB }
check OrderIndependent for 5 Tuple, 3 Val, 5 int

// Concrete witness: a relation strictly better factorized in [c0,c1,c2].
pred OrderMatters { lt[sizeABC, sizeACB] }
run OrderMatters for 5 Tuple, 3 Val, 5 int
