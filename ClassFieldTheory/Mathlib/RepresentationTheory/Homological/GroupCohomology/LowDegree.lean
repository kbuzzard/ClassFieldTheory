import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

open CategoryTheory

namespace groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

namespace cocycles₂

@[simp, norm_cast] lemma coe_zero : ⇑(0 : cocycles₂ A) = 0 := rfl
@[simp, norm_cast] lemma coe_add (a b : cocycles₂ A) : ⇑(a + b) = a + b := rfl

-- TODO: Replace `coe_mk` in mathlib
@[simp, norm_cast] lemma coe_mk' (f : G × G → A) (hf) : ⇑(⟨f, hf⟩ : cocycles₂ A) = f := rfl

end cocycles₂

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_H2Iso_hom :
    H2π A ≫ (H2Iso A).hom = (shortComplexH2 A).moduleCatLeftHomologyData.π := by simp [H2π]

end groupCohomology
