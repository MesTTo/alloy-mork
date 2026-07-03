// Model 13 — COW node-identity as a staleness oracle (the one MORK-specific piece).
//
// Incremental maintenance skips subtries whose identity is unchanged. Sound ONLY if
// node identity is a COLLISION-FREE function of subtrie content (structural identity,
// as PathMap's shared_node_id / merkleize give), NOT a lossy hash. This pins that:
// a lossy hash makes the skip unsound; structural identity makes it sound.
module fac13_cow_merkle

sig Content {}
sig Node { content: one Content }
sig Id {}
one sig M { id: Node -> one Id }

// the staleness skip is sound iff equal identity implies equal content
pred collisionFree { all m, n: Node | (M.id[m] = M.id[n]) => (m.content = n.content) }

// (1) A lossy hash CAN collide: same id, different content -> the skip misses a real
//     change (unsound). Expect SAT.
run LossyCollisionPossible { not collisionFree } for 5 Node, 3 Id, 4 Content

// (2) Structural identity keyed 1:1 on content (id-equal <=> content-equal) forces
//     collision-freedom, so the skip is sound. Expect UNSAT (no violation).
assert StructuralImpliesSound {
  (all m, n: Node | (m.content = n.content) <=> (M.id[m] = M.id[n])) => collisionFree
}
check StructuralImpliesSound for 5 Node, 3 Id, 4 Content
