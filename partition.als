// Model of the ProductZipper primary-factor work partition.
// Factor 0 is a trie; its VALUE nodes are the primary bindings. Each worker descends
// the trie under a PRUNING rule and PRODUCES the value nodes it reaches. We want the
// produced sets to be a DISJOINT COVER: every binding produced by exactly one worker.
//
// This file models the CURRENT "first-branch" rule to reproduce the fuzz counterexample
// (a single-child chain with values => no branch => no pruning => every worker produces
// every value => overlap).

sig Worker {}

sig Node {
  kids  : set Node,     // child nodes
  owner : one Worker    // the node's deterministic hash-owner
}
one sig Root in Node {}
sig ValueNode in Node {} // the primary bindings

fact Tree {
  all n: Node | lone n.~kids           // at most one parent
  no Root.~kids                         // root has no parent
  all n: Node - Root | one n.~kids      // every non-root has exactly one parent
  all n: Node | n in Root.*kids         // all nodes reachable from root
  no n: Node | n in n.^kids             // acyclic
}

pred isBranch[n: Node] { #n.kids > 1 }

// n is the FIRST branch on its root path: a branch with no branch strictly above it.
pred isFirstBranch[n: Node] {
  isBranch[n] and (no a: n.^(~kids) | isBranch[a])
}

// CURRENT RULE: an edge n->c is pruned for w iff n is the first branch and c is not w's.
pred pruned[w: Worker, n: Node, c: Node] {
  c in n.kids and isFirstBranch[n] and c.owner != w
}

fun liveKids[w: Worker] : Node -> Node {
  { n: Node, c: Node | c in n.kids and not pruned[w, n, c] }
}
fun reach[w: Worker] : set Node { Root.*(liveKids[w]) }
pred produces[w: Worker, v: Node] { v in ValueNode and v in reach[w] }

// Every binding is produced by exactly one worker.
assert DisjointCover {
  all v: ValueNode | one w: Worker | produces[w, v]
}

// The REAL requirement (the merge dedups, so overlap is harmless): every binding is
// produced by AT LEAST one worker. A drop (produced by none) is the fatal bug.
assert Cover {
  all v: ValueNode | some w: Worker | produces[w, v]
}

check DisjointCover for 8 but exactly 2 Worker
check Cover for 8 but exactly 2 Worker

