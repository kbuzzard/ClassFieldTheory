import Mathlib

namespace RepresentationTheory

variable {k G} [CommRing k] [Group G]

open groupCohomology CategoryTheory

@[simp]
lemma Rep.forget₂_obj (M) : (forget₂ (Rep k G) (ModuleCat k)).obj M = M.V := rfl

@[simp]
lemma Rep.forget₂_map {M N : Rep k G} (f : M ⟶ N) : (forget₂ (Rep k G) (ModuleCat k)).map f = f.hom := rfl

noncomputable def groupCohomology.zeroι (X : Rep k G) : H0 X ⟶ X.V :=
  (H0Iso X).hom ≫ ModuleCat.ofHom (Submodule.subtype X.ρ.invariants)

@[reassoc (attr := simp)]
lemma groupCohomology.zeroι_naturality {X Y : Rep k G} (f : X ⟶ Y) :
    groupCohomology.map (.id _) f 0 ≫ groupCohomology.zeroι Y = zeroι X ≫ f.hom := by
  aesop (add simp zeroι)

noncomputable def groupCohomology.zeroEmb : functor k G 0 ⟶ forget₂ (Rep k G) (ModuleCat k) where
  app X := groupCohomology.zeroι X
