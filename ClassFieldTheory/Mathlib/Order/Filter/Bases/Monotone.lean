import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Monotone.Defs

namespace Filter.HasBasis

theorem comp_dense {β ι ι' : Type*} [Preorder ι]
    {F : Filter β} {p : ι → Prop} {p' : ι' → Prop} {g : ι → Set β} (b : F.HasBasis p g)
    (hg : Antitone g) (f : ι' → ι) (hp : ∀ ⦃i'⦄, p' i' → p (f i'))
    (dense : ∀ ⦃i⦄, p i → ∃ i', p' i' ∧ i ≤ f i') :
    F.HasBasis p' (g ∘ f) := by
  refine ⟨fun t ↦ ?_⟩
  rw [b.mem_iff]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ?_, by aesop⟩
  obtain ⟨i', hi'1, hi'2⟩ := dense hi1
  exact ⟨i', hi'1, (hg hi'2).trans hi2⟩

theorem comp_dense' {β ι ι' : Type*} [Preorder ι]
    {F : Filter β} {p : ι → Prop} {p' : ι' → Prop} {g : ι → Set β} (b : F.HasBasis p g)
    (hg : Monotone g) (f : ι' → ι) (hp : ∀ ⦃i'⦄, p' i' → p (f i'))
    (dense : ∀ ⦃i⦄, p i → ∃ i', p' i' ∧ f i' ≤ i) :
    F.HasBasis p' (g ∘ f) := by
  refine ⟨fun t ↦ ?_⟩
  rw [b.mem_iff]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ?_, by aesop⟩
  obtain ⟨i', hi'1, hi'2⟩ := dense hi1
  exact ⟨i', hi'1, (hg hi'2).trans hi2⟩

end Filter.HasBasis
