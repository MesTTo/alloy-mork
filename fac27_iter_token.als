-- fac27_iter_token: soundness of the u64 trie iteration token (PathMap dense byte-node)
--
-- PathMap's TrieNode iteration used a 128-bit token because the dense byte-node cached the
-- remaining mask word inside the token. The u64 replacement keeps only a node-local cursor:
-- the token is one more than the last byte visited (0 at the start), and the next byte is
-- recomputed from the node's own mask as the minimum set byte >= token (next_iter_byte_from).
--
-- This model pins the walk's contract:
--   WalkExactAscending  — starting from token 0 and repeatedly stepping visits exactly the
--                         mask's bytes, each exactly once, in ascending order
--   ResumeStrictlyAfter — iter_token_for_path(k) = k+1 resumes the walk over exactly the
--                         bytes strictly greater than k (the old 128-bit scheme's semantics)
--
-- The Rust-side word-boundary test (bytes 63/64, 127/128, 191/192, 255) checks the same
-- contract at the u64-word seams the model abstracts away.
--
-- verdict: both asserts UNSAT (hold in scope), witness run SAT.

open util/ordering[Step]

sig Byte { }
one sig Node { mask: set Byte, le: Byte -> Byte }

-- `le` is a total order on bytes (the 0..255 order, abstracted)
fact ByteOrder {
  all b: Byte | b -> b in Node.le
  all a, b: Byte | (a -> b in Node.le and b -> a in Node.le) implies a = b
  all a, b, c: Byte | (a -> b in Node.le and b -> c in Node.le) implies a -> c in Node.le
  all a, b: Byte | a -> b in Node.le or b -> a in Node.le
}

pred lt[a, b: Byte] { a -> b in Node.le and a != b }

-- next_iter_byte_from(start): the minimum mask byte >= start; the walk step from a visited
-- byte v uses start = v+1, which over a total order is exactly "minimum mask byte > v"
fun nextAfter[v: Byte]: set Byte {
  { b: Node.mask | lt[v, b] and (no c: Node.mask | lt[v, c] and lt[c, b]) }
}
fun first: set Byte {
  { b: Node.mask | no c: Node.mask | lt[c, b] }
}

-- A Step sequence tracing the walk: each step visits one byte or is done
sig Step { visits: lone Byte }
fact Walk {
  -- the first step visits the minimum mask byte (token 0: nothing excluded)
  first[].visits = first
  -- each later step visits the successor of the previous visit; done stays done
  all s: Step - ordering/first |
    let p = s.prev | (some p.visits implies s.visits = nextAfter[p.visits] else no s.visits)
}

assert WalkExactAscending {
  -- every mask byte is visited exactly once, and visits ascend
  (some Node.mask implies Step.visits = Node.mask) and
  (no Node.mask implies no Step.visits) and
  (all disj s, t: Step | (some s.visits and some t.visits and s in ordering/prevs[t]) implies lt[s.visits, t.visits]) and
  (all disj s, t: Step | (some s.visits and some t.visits) implies s.visits != t.visits)
}

assert ResumeStrictlyAfter {
  -- resuming from any byte k yields, as the set reachable by the step relation, exactly
  -- the mask bytes strictly greater than k
  all k: Byte |
    let resumed = { b: Node.mask | lt[k, b] } |
      (some resumed implies
        (nextAfter[k] in resumed and
         all b: resumed - nextAfter[k] | some v: resumed | b in nextAfter[v]))
      and (no resumed implies no nextAfter[k])
}

check WalkExactAscending for exactly 8 Byte, exactly 9 Step
check ResumeStrictlyAfter for exactly 8 Byte, exactly 9 Step

-- witness: a non-trivial mask walks
run { #Node.mask >= 3 and #Byte = 8 } for exactly 8 Byte, exactly 9 Step
