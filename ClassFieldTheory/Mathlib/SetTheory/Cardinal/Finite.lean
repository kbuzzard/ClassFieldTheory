import Mathlib.SetTheory.Cardinal.Finite

namespace Nat

-- TODO: Rename `Nat.card_ne_zero` to `Nat.card_ne_zero_iff`
@[simp] lemma card_ne_zero' {α : Type*} [Nonempty α] [Finite α] : Nat.card α ≠ 0 :=
  Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩

end Nat
