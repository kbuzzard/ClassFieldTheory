import Mathlib

namespace RepresentationTheory

variable {k G} [CommRing k] [Group G]

noncomputable def Invariants.map {A B : Rep k G} (f : A ⟶ B) : ModuleCat.of k A.ρ.invariants ⟶
  ModuleCat.of k B.ρ.invariants := ModuleCat.ofHom <|
  (f.hom.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (Rep.hom_comm_apply f g c).symm
      simp_all [hc g]

lemma notfun {A B : Rep k G} (f : A ⟶ B) : (Rep.invariantsFunctor k G).map f = Invariants.map f := rfl

variable (A B : Rep k G)

open groupCohomology CategoryTheory

lemma commSq1 (f : A ⟶ B): Invariants.map f ≫ (H0Iso B).inv =
    (H0Iso A).inv ≫ groupCohomology.map (MonoidHom.id G) f 0 := by
  rw [← notfun]
  rw [eq_comm, Iso.inv_comp_eq, <- Category.assoc, Iso.eq_comp_inv]
  exact map_id_comp_H0Iso_hom f

-- example (A B : ModuleCat k) (e1 : A ≅ B) (e2 : C ≅ D) (f : A' ⟶ B) :

lemma commSq' (f : A ⟶ B): (H0Iso A).hom ≫ Invariants.map f =
    groupCohomology.map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom := by
  rw [← notfun, groupCohomology.map_id_comp_H0Iso_hom]

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
