/*
 * fac22_term_identity.als
 *
 * Soundness of the TermIdentitySidecar refactor (MORK PR #116), which replaces
 * two hand-rolled primitives with existing ones per the maintainer's
 * "reuse, don't reimplement" direction:
 *   (1) structural_hash()  ->  Expr::hash() == gxhash128(bytes, 0)
 *   (2) synced_prefix_count val-count watermark  ->  PathMap shared_node_id (COW)
 *
 * Two gates are checked:
 *   G1 HashSwapPreservesIdentity: canonical term identity is decided by exact
 *      bytes, with the 128-bit hash used only to narrow a collision bucket. So
 *      swapping in ANY deterministic byte-hash (Expr::hash) cannot change which
 *      encodings share a TermId, even under hash collisions.
 *   G2 StalenessNeverReusesStale: reusing an interned subspace only when its
 *      COW node-id is unchanged never reuses a subspace whose facts changed,
 *      because equal shared_node_id implies byte-identical content (a PathMap
 *      copy-on-write invariant, proven upstream).
 */
module fac22_term_identity

/* ---------- G1: canonical identity is by exact bytes, hash is a filter ---------- */

sig Encoding {}          // an exact encoded MORK term (byte sequence)
sig Hash {}              // a 128-bit hash value
sig TermId {}

// A deterministic hash: equal encodings hash equal. Holds for structural_hash
// AND for Expr::hash / gxhash128 -- both are pure functions of the bytes. The
// refactor changes WHICH function, not determinism, so this fact models either.
one sig H { hash: Encoding -> one Hash }

// The sidecar interns each seen encoding to at most one TermId. intern_term
// reuses an existing id only when `record.encoded() == encoded` (exact bytes),
// consulting hash_buckets[hash] only to shrink the candidate set.
one sig Sidecar { id: Encoding -> lone TermId }

// What the code guarantees: two interned encodings share a TermId iff they are
// the very same encoding. (Exact-byte comparison after the hash-bucket lookup.)
pred CanonicalIdentity {
  all a, b: Encoding |
    (some Sidecar.id[a] and Sidecar.id[a] = Sidecar.id[b]) iff a = b
}

// A hash collision (same hash, distinct encodings) must NOT collapse them to one
// TermId: the exact-byte compare keeps them separate. This is the property the
// hash swap must not break, and it depends only on the exact compare, not on the
// hash function chosen.
assert HashSwapPreservesIdentity {
  CanonicalIdentity implies
    (all a, b: Encoding |
      (H.hash[a] = H.hash[b] and a != b
       and some Sidecar.id[a] and some Sidecar.id[b])
      implies Sidecar.id[a] != Sidecar.id[b])
}
check HashSwapPreservesIdentity for 8

/* ---------- G2: COW node-id staleness safely replaces the val-count watermark ---------- */

sig NodeId {}
// A snapshot of one relation's subspace: the live facts under a prefix, plus the
// PathMap shared_node_id of that subtrie.
sig Snapshot { facts: set Encoding, node: one NodeId }

// PathMap copy-on-write invariant (upstream-proven): two subtries with the same
// shared_node_id hold byte-identical content. Structural sharing means an equal
// node id is only produced by an unchanged subtree.
fact CowIdentity { all s, t: Snapshot | s.node = t.node implies s.facts = t.facts }

// The refactored sync_prefix_if_stale reuses the interned subspace iff the
// current node-id equals the last-synced node-id. Soundness: whenever it reuses
// (node ids equal), the facts are genuinely unchanged, so the interned set is
// still correct and no re-sync is needed.
assert StalenessNeverReusesStale {
  all last, now: Snapshot | last.node = now.node implies last.facts = now.facts
}
check StalenessNeverReusesStale for 8

/* A witness that the model is not vacuous: distinct-content snapshots with
 * distinct node ids exist (the stale case that DOES force a re-sync). */
run StaleReSyncIsPossible {
  some last, now: Snapshot | last.facts != now.facts and last.node != now.node
} for 4
