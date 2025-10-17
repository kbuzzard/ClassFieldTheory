import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso

@[simp] lemma map_lt_one_iff {F α β : Type*} [Preorder α] [Preorder β]
    [MulOneClass α] [MulOneClass β] [EquivLike F α β] [OrderIsoClass F α β] [MulEquivClass F α β]
    (f : F) {x : α} : f x < 1 ↔ x < 1 :=
  map_one f ▸ map_lt_map_iff f
