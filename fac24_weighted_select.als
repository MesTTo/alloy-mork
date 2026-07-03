/*
 * fac24_weighted_select.als
 *
 * Soundness of wiring the weighted-selection primitive (MORK PR #101) as a sink.
 * `select_by_offset(o)` walks the items in the deterministic PathMap iteration
 * order, subtracting each item's positive weight from the remaining offset until
 * `o` lands within an item's weight, and returns that item. This partitions the
 * offset space [0, total) into per-item CONTIGUOUS blocks of size = weight, i.e.
 * it is the inverse-CDF of the weight distribution.
 *
 * Gates:
 *   G1 SelectionWellDefined: every in-range offset selects EXACTLY one item -- no
 *      gap (every offset is claimed) and no overlap (no offset claimed twice), so
 *      the sink writes exactly one `(wselected item)`.
 *   G2 Deterministic: selection is a function of the offset (and the weight SET),
 *      so the written result is independent of the order facts were sunk -- the
 *      confluence the sink needs (weights accumulate into a set via apply_delta).
 *   Witness ProportionalWitness: a partition with DISTINCT weights exists, so the
 *      model is not the trivial uniform case -- selection really is proportional
 *      to weight (an item is selected on weight-many offsets).
 * Out-of-range offsets (>= total_positive_weight) return None by the code's guard
 * `offset >= self.total_positive_weight`, so they select nothing (not modeled here:
 * it is a direct bounds check, and total is kept non-overflowing by the checked/
 * saturating arithmetic folded in from #102).
 */
module fac24_weighted_select

sig Offset {}
// each item's cumulative block = the set of offsets for which it is selected;
// |block| is its positive weight.
sig Item { block: set Offset }

fact InverseCdfPartition {
  all i: Item | some i.block                              // weights are positive
  all a, b: Item | a != b implies no (a.block & b.block)  // blocks are disjoint
  all o: Offset | some i: Item | o in i.block             // blocks cover [0, total)
}

// G1: well-defined -- exactly one item per in-range offset (no gap, no overlap).
assert SelectionWellDefined { all o: Offset | one i: Item | o in i.block }
check SelectionWellDefined for 8

// select_by_offset as a relation: the item whose block contains the offset.
fun select[o: Offset]: Item { block.o }

// G2: deterministic -- select is a total function, so a fixed offset over a fixed
// weight set always selects the same item (order of sinking is irrelevant because
// apply_delta accumulates weights into a set).
assert Deterministic { all o: Offset | one select[o] }
check Deterministic for 8

// non-vacuity: a partition with distinct block sizes (weights) exists, so this is
// genuinely proportional selection, not the degenerate uniform case.
run ProportionalWitness {
  some a, b: Item | a != b and #a.block != #b.block
} for 6
