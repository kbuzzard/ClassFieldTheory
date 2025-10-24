import Mathlib.Data.Finsupp.Single

namespace Finsupp
variable {α M : Type*} [Zero M]

instance instSubsingleton [IsEmpty α] : Subsingleton (α →₀ M) where
  allEq f g := by ext x; exact isEmptyElim x

lemma nontrivial_iff : Nontrivial (α →₀ M) ↔ Nonempty α ∧ Nontrivial M where
  mp := by
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ g a := by simpa [Finsupp.ext_iff] using hfg
    exact ⟨⟨a⟩, _, _, ha⟩
  mpr | ⟨_, _⟩ => inferInstance

end Finsupp
