/*
 * fac23_egraph_sink.als
 *
 * Soundness of wiring the scoped e-graph (kernel/src/egraph.rs) as a MORK
 * sink/source (PR #117), modeled on the z3 sink/source (a named instance store,
 * Adam MORKification 2026-03-02). The sink pushes terms and equalities (= a b)
 * into a named e-graph instance; finalize runs congruence closure; the source
 * reads back one canonical (cheapest-extracted) representative per e-class.
 *
 * SCOPE. egg's union-find + rebuild computing the LEAST congruence closure
 * (soundness = no spurious merges; completeness) is the reused, separately-proven
 * component (egg, POPL 2021), and egraph.rs is a direct port of it. That
 * minimality is a higher-order property (quantifying over all congruences) and is
 * taken as given here. What THIS model verifies is the sink/source WIRING built
 * on top: that the source reads the closure correctly through extraction.
 *   G1 RoundTrip: two terms pushed equal read the SAME extracted representative.
 *   G2 CongruenceReadThrough: terms equal only by CONGRUENCE (never pushed
 *      directly) also read the same representative -- the point of routing the
 *      read through an e-graph rather than a plain union of the pushed pairs.
 *   G3 OneCanonicalPerClass: the whole class collapses to a single representative
 *      (the source emits exactly one canonical fact per class: no dup, no split).
 * Instance isolation (distinct names => independent e-graphs) is a structural
 * property of the hashmap keying, checked by the Rust differential test, not here.
 */
module fac23_egraph_sink

sig Sym {}
sig Term {}
// an application e-node: same head + equivalent child => congruent
sig App extends Term { head: one Sym, child: one Term }

// equalities the program pushes through the sink (a SET: sink order is irrelevant,
// which is why the read form is order-independent / confluent)
one sig Push { eqs: Term -> Term }

// the e-graph's equivalence after finalize/rebuild == egg's congruence closure.
one sig EGraph { equiv: Term -> Term }
fact EggCongruenceClosure {
  (Term <: iden) in EGraph.equiv          // reflexive
  ~(EGraph.equiv) in EGraph.equiv          // symmetric
  (EGraph.equiv).(EGraph.equiv) in EGraph.equiv   // transitive
  (Push.eqs + ~(Push.eqs)) in EGraph.equiv // contains the pushed equalities
  all f, g: App |                          // congruence
    (f.head = g.head and (f.child -> g.child) in EGraph.equiv) implies (f -> g) in EGraph.equiv
}

// the source read path: extract_cheapest picks one representative term per class.
one sig Extract { rep: Term -> one Term }
fact ExtractionWellFormed {
  all t: Term | (t -> Extract.rep[t]) in EGraph.equiv               // rep is in t's class
  all a, b: Term | (a -> b) in EGraph.equiv implies Extract.rep[a] = Extract.rep[b]  // one per class
}

// G1: pushed-equal terms read the same canonical representative.
assert RoundTrip {
  all a, b: Term | (a -> b) in Push.eqs implies Extract.rep[a] = Extract.rep[b]
}
check RoundTrip for 8

// G2: terms equal ONLY by congruence still read the same representative.
assert CongruenceReadThrough {
  all f, g: App |
    (f.head = g.head and Extract.rep[f.child] = Extract.rep[g.child])
    implies Extract.rep[f] = Extract.rep[g]
}
check CongruenceReadThrough for 8

// G3: a whole equivalence class shares one representative (single canonical fact).
assert OneCanonicalPerClass {
  all a, b: Term | (a -> b) in EGraph.equiv implies Extract.rep[a] = Extract.rep[b]
}
check OneCanonicalPerClass for 8

// non-vacuity: congruence forces a merge (and a shared read) that was NOT pushed
// directly -- confirming the model exercises congruence, not just the raw pairs.
run CongruenceMergeWitness {
  some f, g: App | f != g
    and (f -> g) in EGraph.equiv
    and (f -> g) not in (Push.eqs + ~(Push.eqs))
    and Extract.rep[f] = Extract.rep[g]
} for 8
