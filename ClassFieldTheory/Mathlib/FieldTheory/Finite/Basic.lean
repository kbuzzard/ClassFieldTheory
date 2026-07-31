module

public import Mathlib.FieldTheory.Finite.Basic

public section

theorem FiniteField.pow_natCard {K : Type*} [GroupWithZero K] [Finite K] (a : K) :
    a ^ Nat.card K = a := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, pow_card]
