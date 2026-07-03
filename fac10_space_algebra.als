// Model 10 — Space algebra: the RING law that makes factorization/F-IVM apply.
//
// Space-Operations (wiki) gives MORK a ring: union `|`, intersection `&`,
// subtraction `\`, composition `.`. F-IVM and factorized representations rely on
// composition DISTRIBUTING over union (that is what lets a product be pushed
// through a union without expanding it). This checks that law on trie paths.
module fac10_space_algebra

sig Path {}
one sig M { cat: Path -> Path -> Path }               // concatenation p ++ e = pe
fact catFunctional { all p, e: Path | lone p.(M.cat)[e] }

fun compose[a: set Path, b: set Path]: set Path {      // {p ++ e | p in a, e in b}
  { pe: Path | some p: a, e: b | pe in p.(M.cat)[e] }
}

// Composition distributes over union (the factorization / F-IVM enabler). Expect UNSAT.
assert ComposeDistributesUnion {
  all x, y, z: set Path | compose[x, y + z] = compose[x, y] + compose[x, z]
}
check ComposeDistributesUnion for 5 Path

// Sanity: subtraction and intersection partition the left operand. Expect UNSAT.
assert SubtractUnionPartition { all x, y: set Path | (x - y) + (x & y) = x }
check SubtractUnionPartition for 5 Path
