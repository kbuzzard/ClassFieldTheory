import Mathlib.RepresentationTheory.Rep

open CategoryTheory

namespace Rep
variable {R G : Type} [CommRing R] [Group G]

-- TODO : add in mathlib, see GroupCohomology.IndCoind.TrivialCohomology
--attribute [simps obj_ρ] trivialFunctor

@[simps]
def mkIso (M₁ M₂ : Rep R G) (f : M₁.V ≅ M₂.V)
    (hf : ∀ g : G, ∀ m : M₁, f.hom (M₁.ρ g m) = M₂.ρ g (f.hom m) := by aesop) : M₁ ≅ M₂ where
  hom.hom := f.hom
  inv.hom := f.inv
  inv.comm g := by rw [f.comp_inv_eq, Category.assoc, eq_comm, f.inv_comp_eq]; aesop

end Rep
