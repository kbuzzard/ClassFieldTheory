import Mathlib.RepresentationTheory.Rep

open
  Finsupp
  Representation
  Rep
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits

variable {R G S A : Type} [CommRing R] [Group G] [Group S] {M : Rep R G} {A : ModuleCat R}

namespace Rep

-- TODO : add in mathlib, see GroupCohomology.IndCoind.TrivialCohomology
--attribute [simps obj_ρ] trivialFunctor

@[simps]
def mkIso (M₁ M₂ : Rep R G) (f : M₁.V ≅ M₂.V) (hf : ∀ g : G, ∀ m : M₁, f.hom (M₁.ρ g m) = M₂.ρ g (f.hom m)) : M₁ ≅ M₂ where
  hom := {
    hom := f.hom
    comm g := by aesop_cat
  }
  inv := {
    hom := f.inv
    comm g := by
      rw [f.comp_inv_eq, Category.assoc, eq_comm, f.inv_comp_eq]
      aesop
  }
  hom_inv_id := by aesop
  inv_hom_id := by aesop

end Rep
