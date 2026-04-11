module

public import
  ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
TODO : Although we made `Rep.res` a `def` there is still places we need to unfold the definition
-- inside `simp`. The goal usually involves `groupCohomology.map` and the reason being is that
-- `groupCohomology.map` uses `Action.res` directly, so what we should do is
-- 1. PR `Rep.res` into mathlib and change the defition of `groupCohomology.map` to use `Rep.res`
-- 2. refactor `Rep` in mathlib to be a `def` instead of `abbrev` which (after test in CFT repo)
-- seems to solve some of our problems.
-/

@[expose] public section

open
  Rep
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

universe t w w' u v0 v1 v2
variable {R : Type u} {G : Type v0} {H : Type v1} {K : Type v2} [CommRing R]

noncomputable section

namespace Rep

/--
If `M` is an object of `Rep R G` and `φ : H →* G` then `M ↓ φ` is the restriction of the
representation `M` to `H`, as an object of `Rep R H`.

This is notation for `(Rep.res H).obj M`, which is an abbreviation of
`(Action.res (ModuleCat R) H.subtype).obj M`
-/
notation3:60 M:60 " ↓ " f:61 => res f M

section monoid

variable [Monoid G] [Monoid H] [Monoid K]

abbrev resComp (f : H →* G) (g : K →* H) :
    resFunctor (f.comp g) ≅ resFunctor (k := R) f ⋙ resFunctor g :=
  NatIso.ofComponents (fun A ↦ mkIso (.mk (LinearEquiv.refl _ _) <| fun _ ↦ by simp))

abbrev resCongr {f1 f2 : H →* G} (h : f1 = f2) :
    resFunctor.{w} (k := R) f1 ≅ resFunctor f2 :=
  NatIso.ofComponents (fun A ↦ mkIso (.mk (LinearEquiv.refl _ _) <| fun _ ↦ by simp [h]))

set_option backward.isDefEq.respectTransparency false in
variable (R) in
def resEquiv (f : H ≃* G) : Rep.{w} R G ≌ Rep.{w} R H where
  functor := resFunctor f.toMonoidHom
  inverse := resFunctor f.symm.toMonoidHom
  unitIso := resCongr f.coe_monoidHom_comp_coe_monoidHom_symm.symm ≪≫ resComp _ _
  counitIso := (resComp _ _).symm ≪≫ resCongr f.coe_monoidHom_symm_comp_coe_monoidHom

@[simp] lemma resEquiv_functor (f : H ≃* G) :
    (resEquiv R f).functor = resFunctor f := rfl
@[simp] lemma resEquiv_inverse (f : H ≃* G) :
    (resEquiv R f).inverse = resFunctor f.symm := rfl

variable (φ : H →* G)

instance : Limits.HasLimits (Rep.{w} R G) :=
  Adjunction.has_limits_of_equivalence toModuleMonoidAlgebra

instance : Limits.HasColimits (Rep.{w} R G) :=
  Adjunction.has_colimits_of_equivalence toModuleMonoidAlgebra

instance : Limits.ReflectsLimitsOfSize.{w, w} (forget₂ (Rep.{w} R G) (ModuleCat R)) :=
  Limits.reflectsLimits_of_reflectsIsomorphisms

instance : Limits.PreservesLimits (resFunctor.{w} (k := R) φ) :=
  have : PreservesLimitsOfSize.{w, w} (resFunctor φ ⋙ forget₂ (Rep.{w} R H) (ModuleCat R)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} R G) (ModuleCat R)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R H) (ModuleCat R))

instance : Limits.ReflectsColimitsOfSize.{w, w} (forget₂ (Rep.{w} R H) (ModuleCat R)) :=
  reflectsColimits_of_reflectsIsomorphisms

instance : Limits.PreservesColimits (resFunctor.{w} (k := R) φ) :=
  have : PreservesColimitsOfSize.{w, w} (resFunctor (k := R) φ ⋙
      forget₂ (Rep.{w} R H) (ModuleCat R)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} R G) (ModuleCat R)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R H) (ModuleCat R))

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness.
TODO : generalize the universe
-/
lemma res_map_ShortComplex_Exact (φ : H →* G)
    (S : ShortComplex (Rep.{u} R G)) [Small.{u} R] :
    (S.map (resFunctor φ)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

/--
An object of `Rep R G` is zero iff the underlying `R`-module is zero.
-/
lemma isZero_iff (M : Rep R G) : IsZero M ↔ Subsingleton M.V := by
  simp [IsZero.iff_id_eq_zero, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff,
    ← ModuleCat.isZero_of_iff_subsingleton (R := R), ModuleCat.hom_ext_iff]


/--
An object of `Rep R G` is zero iff its restriction to `H` is zero.
-/
lemma isZero_res_iff (M : Rep R G) {H : Type u} [Group H] (φ : H →* G) :
    IsZero (M ↓ φ) ↔ IsZero M := by
  rw [isZero_iff, isZero_iff, Rep.res_obj_V]

/--
The restriction functor `res φ : Rep R G ⥤ Rep R H` takes short exact sequences to short
exact sequences.
-/
@[simp] lemma shortExact_res (φ : H →* G) {S : ShortComplex (Rep.{u} R G)} :
    (S.map (resFunctor φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
      Representation.IntertwiningMap.coe_eq_toLinearMap, mono_iff_injective, hom_ofHom,
      Representation.IntertwiningMap.coe_mk, Representation.IntertwiningMap.coe_toLinearMap,
      ShortComplex.map_X₃, ShortComplex.map_g, epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injective _|>.2 h₂, epi_g := epi_iff_surjective _|>.2 h₃}
  · rintro ⟨h⟩
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simp_all [mono_iff_injective]
      epi_g := by simp_all [epi_iff_surjective]
    }
end monoid

section

@[simp] lemma norm_hom_res [Group G] [Group H] [Fintype G] [Fintype H] (M : Rep.{w} R G)
    (e : H ≃* G) : (res e.toMonoidHom M).norm.hom.toLinearMap = M.norm.hom.toLinearMap := by
  ext
  simp [res_obj_V, norm, Representation.norm, res_obj_ρ, ← e.toEquiv.sum_comp]

end

end Rep

namespace groupCohomology

variable {G S S' : Type u} [Group G] [Group S] (φ : S →* G) [Group S'] (ψ : S' →* S)
  {M : Rep.{u} R G}

/--
The restriction map `Hⁿ(G,M) ⟶ Hⁿ(H,M)`, defined as a morphism of functors
-/
def rest (n : ℕ) : functor R G n ⟶ Rep.resFunctor φ ⋙ functor R S n  where
  app M               := map φ (𝟙 (M ↓ φ)) n
  naturality M₁ M₂ f  := by
    simp only [functor_obj, Functor.comp_obj, functor_map, Functor.comp_map]
    rw [←map_comp, ←map_comp]
    congr 1

lemma rest_app (n : ℕ) (M : Rep R G) :
    (rest φ n).app M = map φ (𝟙 (M ↓ φ)) n := rfl

lemma rest_id (n : ℕ) : rest (MonoidHom.id G) (R := R) n = 𝟙 (functor R G n) := by
  ext M : 2
  rw [rest_app]
  apply map_id

set_option backward.isDefEq.respectTransparency false in
lemma rest_comp (n : ℕ) : rest (φ.comp ψ) n = rest φ (R := R) n ≫ (𝟙 _ ◫ rest ψ n) := by
  ext M : 2
  simp only [functor_obj, Functor.comp_obj, Functor.id_hcomp, NatTrans.comp_app,
      Functor.whiskerLeft_app, rest_app]
  rw [← map_comp]
  exact map_congr rfl rfl n


/--
Given any short exact sewuence `0 → A → B → C → 0` in `Rep R G` and any
subgroup `H` of `G`, the following diagram is commutative

  Hⁿ(G,C) ⟶ H^{n+1}(G A)
      |         |
      ↓         ↓
  Hⁿ(H,C) ⟶ H^{n+1}(G A).

The vertical arrows are restriction and the horizontals are connecting homomorphisms.

For this, it would be sensible to define restriction as a natural transformation, so that it
automatically commutes with the other maps. This requires us to first define cohomology as a
functor.
-/
lemma rest_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    {H : Type u} [Group H] (φ : H →* G) (i j : ℕ) (hij : i + 1 = j) :
    δ hS i j hij ≫ (rest φ j).app S.X₁ = (rest φ i).app S.X₃ ≫ δ ((shortExact_res φ).2 hS) i j hij
    := by
  let C₁ := S.map (cochainsFunctor R G)
  let C₂ := (S.map (resFunctor φ)).map (cochainsFunctor R H)
  have ses₁ : C₁.ShortExact := map_cochainsFunctor_shortExact hS
  have ses₂ : C₂.ShortExact := by
    apply map_cochainsFunctor_shortExact
    rwa [shortExact_res]
  let this : C₁ ⟶ C₂ := {
    τ₁ := cochainsMap φ (𝟙 (res φ S.X₁))
    τ₂ := cochainsMap φ (𝟙 (res φ S.X₂))
    τ₃ := cochainsMap φ (𝟙 (res φ S.X₃))
  }
  exact HomologicalComplex.HomologySequence.δ_naturality this ses₁ ses₂ i j hij

set_option backward.isDefEq.respectTransparency false in
noncomputable def resSubtypeRangeIso (M : Rep.{u} R G) {H : Type u} [Group H] (f : H →* G) (n : ℕ)
    (hf : Function.Injective f) :
    groupCohomology (M ↓ f.range.subtype) n ≅ groupCohomology (M ↓ f) n where
  hom := groupCohomology.map f.rangeRestrict (Rep.ofHom ⟨LinearMap.id, by simp⟩) _
  inv := groupCohomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom
      (Rep.ofHom ⟨LinearMap.id, by simp⟩) _
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by ext; simp) (by simp) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    refine groupCohomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by simp) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupCohomology

namespace groupHomology

variable {G S S' : Type u} [Group G] [Group S] (φ : S →* G) [Group S'] (ψ : S' →* S)
  {M : Rep.{u} R G}

set_option backward.isDefEq.respectTransparency false in
noncomputable def resSubtypeRangeIso (M : Rep R G) {H : Type u} [Group H] (f : H →* G) (n : ℕ)
    (hf : Function.Injective f) :
    groupHomology (M ↓ f.range.subtype) n ≅ groupHomology (M ↓ f) n where
  hom := groupHomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom
      (Rep.ofHom ⟨LinearMap.id (M := M.V), by simp⟩) _
  inv := groupHomology.map f.rangeRestrict (Rep.ofHom ⟨.id (M := M.V), by simp⟩) _
  hom_inv_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by ext; simp) (by simp) n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    refine groupHomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by simp) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupHomology

end
