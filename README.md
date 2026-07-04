# Alloy MORK

Formal [Alloy](https://alloytools.org/) models of MORK's correctness-critical mechanics and the
asymptotic optimizations built on top of them. Each model is a small, bounded-scope specification
that either proves an invariant holds (no counterexample in scope) or exhibits the counterexample
that pins a requirement. Several caught real bugs before any Rust was written.

MORK is a minimal-MeTTa graph-rewrite engine over a 256-radix byte trie (PathMap). These models
cover its join, matcher, fixpoint, copy-on-write sharing, and the hypertree-decomposition /
factorized-aggregation work.

## Running

```
java -jar ~/.local/share/alloy/alloy.jar exec facN.als
```

Reading the output: `check ... UNSAT` means the assertion holds (no counterexample within the
scope); `SAT` means a counterexample was found. For a `run`, `SAT` means a witness exists. Alloy's
small-scope hypothesis makes a clean UNSAT strong evidence, not an all-sizes proof; the Rust side
carries differential oracles, and Isabelle is used where an all-sizes proof is wanted.

## The models

| file | verdict | what it establishes |
|------|---------|---------------------|
| `fac1_order` | SAT witness | trie factorization is order-dependent (a relation is compact in one column order, flat in another) |
| `fac2_fixpoint` | Conflict UNSAT | **theorem**: one canonical trie order is scan-free for a fixpoint iff the rules' bound-column-sets form a chain under subset; incomparable sets force a flat scan |
| `fac6_drep_cover` | SAT/UNSAT/SAT | Dilworth: the minimum number of trie orders (a d-representation) equals the max antichain of the bound-set poset (a 3-antichain needs exactly 3) |
| `fac7_factorized_match` | UNSAT/SAT | matching a pattern directly on un-expanded factorized output is sound; the wrong pruning is caught |
| `fac4_incremental` | UNSAT/SAT | the incremental self-join delta rule `dJ = D∘R' ∪ R∘D` is exact; the tempting shortcut drops tuples |
| `fac8_seminaive_fixpoint` | UNSAT/SAT | semi-naive evaluation equals naive **only under the closure invariant**; without it, facts are missed |
| `fac5_cow_staleness` | UNSAT/SAT | incremental recomputation must key on the **join variable** subtries, not the output-variable subtries |
| `fac13_cow_merkle` | SAT/UNSAT | the COW node-identity staleness skip is sound iff identity is **structural** (collision-free), not a lossy hash |
| `fac9_coref_match` | UNSAT/SAT | coreferential (repeated-variable) matching is a real restriction; ignoring it is unsound |
| `fac10_space_algebra` | UNSAT | the space is a ring: composition distributes over union (the factorization / F-IVM enabler) |
| `fac14_ghd` | UNSAT/SAT | generalized hypertree decomposition is sound: under the cover condition, the join of the bags equals the join of all relations |
| `fac16_pushdown` | UNSAT/SAT | projection pushdown is sound **only for a variable local to one relation** — a join variable cannot be pushed out, which is why WCO enumeration cannot be beaten |
| `fac17_count` | UNSAT/SAT | factorized aggregation: `|R⋈S| = Σ_y |R_y|·|S_y|` equals enumerate-and-count while touching fewer rows — the asymptotic win WCO cannot match |
| `fac18_count_routing` | UNSAT/SAT | routing the CountSink to the factorized engine is sound iff the projection keeps all variables: distinct-output count equals match count under a full projection, and strictly undercounts once a variable is dropped |
| `fac19_semijoin_domain` | UNSAT/SAT | routing the SumSink (SUM DISTINCT of a column) is sound via Yannakakis semi-join reduction: the free-variable EXISTS-elimination domain equals the join's projection onto that column, and a dangling tuple (no join partner) is correctly excluded |
| `fac20_grouping_decline` | UNSAT/SAT | the aggregate gate must decline grouping: with no grouping variable the aggregate is one total fact (matches the scalar), but a grouping variable can emit one fact per distinct value, more than the single scalar |
| `fac21_sumsum_not_sumprod` | SAT/UNSAT | SUM(DISTINCT) is not a COUNT-style weight-swap: weighting each fact by its column value sums with multiplicity and disagrees with the distinct sum once a value repeats; they coincide only for an injective column (so the semi-join domain is required) |
| `fac22_term_identity` | UNSAT/UNSAT/SAT | the term-identity sidecar refactor is sound: the `structural_hash`→`Expr::hash` swap preserves canonical identity (the 128-bit hash is only a collision-bucket filter; exact bytes decide, so any deterministic hash is safe), and the COW `shared_node_id` staleness never reuses a subspace whose facts changed |
| `fac23_egraph_sink` | UNSAT×3/SAT | wiring the scoped e-graph as a sink/source is sound: taking egg's congruence closure as given, the source reads it correctly through extraction — terms pushed equal and terms equal only by congruence both read the same cheapest-extracted representative, exactly one canonical per class |
| `fac24_weighted_select` | UNSAT/UNSAT/SAT | wiring the weighted-selection primitive (#101) as a sink is sound: `select_by_offset` partitions the offset space [0,total) into per-item contiguous blocks sized by weight, so selection is well-defined (exactly one item per in-range offset) and deterministic (a function of the offset and the accumulated weight set), and the proportional (distinct-weight) case is realizable |
| `fac25_exec_dispatch` | UNSAT×3/SAT | the exec special-form dispatch is a total contract: every valid functor combination (`,`/`I` pattern × `,`/`O` template) routes to exactly one transform kernel, every other shape is rejected, and the kernels' io flags mirror the functors exactly (sources iff `I`, sinks iff `O`) — the contract the `exec_special_forms.rs` behavior tests pin against the live engine |
| `fac26_leapfrog_gate` | UNSAT×3/SAT | the #124 leapfrog dispatch gate is sound: the routed join is selected only when the experimental feature AND the runtime toggle AND the flat shape all hold (every other state takes the stock ProductZipper, exactly one engine per state), and with the byte-identity differentials as the agreement premise the observed answers are identical in every gate state — the gate chooses who computes, never what |
| `partition`, `partition2` | UNSAT | the ProductZipper parallel work-partition is a correct cover (single-factor, and across the stitch) |

## The through-line

`fac1`, `fac2`, `fac6`, `fac7` map out where a single-order trie can and cannot be factorized.
`fac4`, `fac5`, `fac8`, `fac13` cover incremental (semi-naive) maintenance and the copy-on-write
staleness oracle. `fac14`, `fac16`, `fac17` are the hypertree-decomposition and
factorized-aggregation line: they establish that the WCO join is output-optimal for *enumeration*
(so it cannot be beaten there), and that the remaining asymptotic win is **aggregation** — a
COUNT/SUM factorizes into a sum-of-products and runs in O(N^fhtw), not O(output). That model drove a
factorized-count implementation on top of MORK's WCO join with a measured, growing speedup
(a dropped exponent, not a constant factor). `fac18` closes the loop to the running system: MORK's
CountSink counts distinct *outputs*, not matches, so it pins the exact gate under which the sink may
be routed to the factorized engine — the projection must keep every variable — and exhibits the
undercount when it does not. `fac19` does the same for the SumSink: a `SUM(DISTINCT col)` routes
through a Yannakakis semi-join reduction, because the free-variable EXISTS-elimination domain of the
summed column equals the join's projection onto it, dangling tuples excluded. `fac20` and `fac21`
pin the two remaining gate decisions: grouping must be declined (a grouping variable emits one fact
per group, not one scalar), and SUM must use the distinct semi-join domain rather than a
weight-swap (which would sum with multiplicity). Together `fac16`-`fac21` are the full soundness
argument for the factorized COUNT/SUM routing wired into MORK.
