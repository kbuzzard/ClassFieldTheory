import Mathlib.GroupTheory.OrderOfElement

variable {M : Type*} [Monoid M] {x : M}

-- TODO: Make `orderOf_eq_zero_iff`/`orderOf_pos_iff` simp
@[to_additive]
lemma orderOf_ne_zero_iff : orderOf x ≠ 0 ↔ IsOfFinOrder x := orderOf_eq_zero_iff.not_left
