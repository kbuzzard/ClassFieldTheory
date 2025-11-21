import Mathlib.Data.Finset.Range

theorem Multiset.toFinset_range {n : ℕ} : (Multiset.range n).toFinset = .range n :=
  Finset.val_injective (Finset.range n).nodup.dedup
