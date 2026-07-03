// DEEPENED model: the TWO-factor ProductZipper with the primary partition.
// Factor 0 (primary) is a trie; at each factor-0 LEAF (stitch point) a copy of factor 1
// (secondary) is grafted. A PRODUCT TUPLE is a pair (factor-0 leaf, factor-1 leaf). The
// primary partition prunes the first-branch children of factor 0 by owner; factor 1 is
// never pruned. We check COVER over product tuples (the merge dedups, so overlap is fine;
// only a DROP is fatal) -- faithfully across the stitch, which the single-trie fuzz/model
// did not exercise.

sig Worker {}

abstract sig Node { owner: one Worker }
sig F0 extends Node { f0kids: set F0 }
sig F1 extends Node { f1kids: set F1 }
one sig F0Root in F0 {}
one sig F1Root in F1 {}

fact F0Tree {
  all n: F0 | lone n.~f0kids
  no F0Root.~f0kids
  all n: F0 - F0Root | one n.~f0kids
  all n: F0 | n in F0Root.*f0kids
  no n: F0 | n in n.^f0kids
}
fact F1Tree {
  all n: F1 | lone n.~f1kids
  no F1Root.~f1kids
  all n: F1 - F1Root | one n.~f1kids
  all n: F1 | n in F1Root.*f1kids
  no n: F1 | n in n.^f1kids
  some n: F1 | no n.f1kids           // at least one factor-1 leaf
}

fun f0leaves: set F0 { {n: F0 | no n.f0kids} }
fun f1leaves: set F1 { {n: F1 | no n.f1kids} }

pred f0branch[n: F0] { #n.f0kids > 1 }
pred isFirstBranch[n: F0] { f0branch[n] and (no a: n.^(~f0kids) | f0branch[a]) }
fun firstBranch: lone F0 { {n: F0 | isFirstBranch[n]} }

// A factor-0 edge into child c of the first branch is pruned for w when c.owner != w.
pred f0pruned[w: Worker, c: F0] {
  some firstBranch and c in firstBranch.f0kids and c.owner != w
}
// Worker w reaches factor-0 node n iff no node on root->n is a pruned first-branch child.
fun f0reached[w: Worker]: set F0 {
  { n: F0 | no c: (n + n.^(~f0kids)) & F0 | f0pruned[w, c] }
}

// Product tuple (l0, l1) produced by w iff w reaches the factor-0 leaf l0 (factor 1 is
// descended fully there, never pruned).
assert Cover {
  all l0: f0leaves, l1: f1leaves | some w: Worker | l0 in f0reached[w]
}

// Also: the FULL FRAGMENT the partition must cover -- every factor-0 leaf reached by someone.
assert LeafCover {
  all l0: f0leaves | some w: Worker | l0 in f0reached[w]
}

check LeafCover for 7 but exactly 2 Worker
check Cover for 6 but exactly 2 Worker, exactly 3 F1
check Cover for 6 but exactly 3 Worker, exactly 2 F1
