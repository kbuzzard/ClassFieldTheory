import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

noncomputable section

open Finsupp

variable {k G : Type} [CommRing k] [Group G]

namespace groupHomology

/-- The trivial `G`-representation on `ℤ` has first homology group `H₁(G, ℤ) ≃+ Gᵃᵇ` defined by
`⟦single g a⟧ ↦ a • ⟦g⟧`. -/
@[simps! -isSimp]
def H1TrivialAddEquiv : H1 (.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  (H1AddEquivOfIsTrivial _).trans (TensorProduct.rid ..).toAddEquiv

@[simp]
lemma H1TrivialAddEquiv_single (g : G) (n : ℤ) :
    H1TrivialAddEquiv (H1π _ <| (cycles₁IsoOfIsTrivial _).inv <| single g n) =
      n • Additive.ofMul (Abelianization.of g) := by
  simp [H1TrivialAddEquiv, H1AddEquivOfIsTrivial_single (A := .trivial ℤ G ℤ)]

@[simp]
lemma H1TrivialAddEquiv_symm (g : G) :
    H1TrivialAddEquiv.symm (.ofMul <| .of g) =
      H1π _ ((cycles₁IsoOfIsTrivial _).inv <| single g 1) := by
  rw [AddEquiv.symm_apply_eq, H1TrivialAddEquiv_single]; simp

end groupHomology
