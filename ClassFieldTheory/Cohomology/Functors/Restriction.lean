import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import ClassFieldTheory.Mathlib.RepresentationTheory.Rep
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Induced

open
  Rep
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H] {M : Rep R G}

noncomputable section

namespace Rep

/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
def res (φ : H →* G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) φ

set_option quotPrecheck false in
/--
If `M` is an object of `Rep R G` and `φ : H →* G` then `M ↓ φ` is the restriction of the
representation `M` to `H`, as an object of `Rep R H`.

This is notation for `(Rep.res H).obj M`, which is an abbreviation of
`(Action.res (ModuleCat R) H.subtype).obj M`
-/
notation3:60 M:60 " ↓ " φ:61 => (res φ).obj M

@[simp] lemma ρ_res_apply (φ : H →* G) (h : H) : (M ↓ φ).ρ h = M.ρ (φ h) := rfl

/-
`simp` lemmas for `Action.res` also work for `Rep.res` because it is an abbreviation:
-/
lemma res_obj_ρ' (M : Rep R G) (H : Type u) [Group H] (φ : H →* G) (h : H) :
  (M ↓ φ).ρ h = M.ρ (φ h) := by simp

lemma res_obj_V (M : Rep R G) (H : Type u) [Group H] (φ : H →* G)  :
  (M ↓ φ).V = M.V := by simp [res]

instance (H : Type u) [Group H] (f : H →* G) : (res (R := R) f).ReflectsIsomorphisms := by
  unfold res
  infer_instance

instance (H : Type u) [Group H] (f : H →* G) :
    PreservesLimitsOfSize.{u, u, u, u, u + 1, u + 1} (res (R := R) f) := by
  unfold res
  infer_instance

instance (H : Type u) [Group H] (f : H →* G) : ReflectsLimits (res (R := R) f) :=
  reflectsLimits_of_reflectsIsomorphisms

instance (R G H : Type u) [CommRing R] [Group G] [Group H] (f : H →* G) :
    PreservesColimits (Action.res (ModuleCat.{u} R) f) :=
  Action.preservesColimitsOfSize_of_preserves (Action.res (ModuleCat.{u} R) f) <|
    Action.preservesColimits_forget ..

instance (R G H : Type u) [CommRing R] [Group G] [Group H] (f : H →* G) :
   ReflectsColimits (Action.res (ModuleCat.{u} R) f) :=
  reflectsColimits_of_reflectsIsomorphisms

instance (H : Type u) [Group H] (f : H →* G) : (res (R := R) f).Faithful := by
  unfold res
  infer_instance

instance (H : Type u) [Group H] (f : H →* G) (S : ShortComplex (Rep R G)) :
    (res (R := R) f).PreservesLeftHomologyOf S := by
  unfold res
  infer_instance

instance (H : Type u) [Group H] (f : H →* G) (S : ShortComplex (Rep R G)) :
    (res (R := R) f).PreservesRightHomologyOf S := by
  unfold res
  infer_instance

instance (H : Type u) [Group H] (φ : H →* G) :
    PreservesFiniteColimits (res (R := R) φ) := by
  unfold res
  infer_instance

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness.
-/
lemma res_map_ShortComplex_Exact (H : Type u) [Group H] (φ : H →* G) (S : ShortComplex (Rep R G)) :
    (S.map (res φ)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

/--
An object of `Rep R G` is zero iff the underlying `R`-module is zero.
-/
lemma isZero_iff (M : Rep R G) : IsZero M ↔ IsZero (M.V) := by
  simp only [IsZero.iff_id_eq_zero]
  apply Action.hom_ext_iff

/--
An object of `Rep R G` is zero iff its restriction to `H` is zero.
-/
lemma isZero_res_iff (M : Rep R G) {H : Type u} [Group H] [DecidableEq H] (φ : H →* G) :
    IsZero (M ↓ φ) ↔ IsZero M := by
  rw [isZero_iff, isZero_iff, Rep.res_obj_V]

/--
The restriction functor `res φ : Rep R G ⥤ Rep R H` takes short exact sequences to short
exact sequences.
-/
@[simp] lemma shortExact_res {H : Type u} [Group H] (φ : H →* G) {S : ShortComplex (Rep R G)} :
    (S.map (Rep.res φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [res, ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
      Functor.mono_map_iff_mono, ShortComplex.map_X₃, ShortComplex.map_g,
      Functor.epi_map_iff_epi] at h₂ h₃ -- don't add res
    exact {
      exact := h₁
      mono_f := h₂
      epi_g := h₃
    }
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa using h₂
      epi_g := by simpa [res] using h₃ -- don't add res
    }

@[simp] lemma norm_hom_res [Fintype G] [Fintype H] (M : Rep R G) (e : H ≃* G) :
    (M ↓ e.toMonoidHom).norm.hom = M.norm.hom := by
  ext
  simp [Representation.norm, ← e.toEquiv.sum_comp]

end Rep

namespace groupCohomology

variable
  {S : Type u} [Group S] (φ : S →* G)
  {S' : Type u} [Group S'] (ψ : S' →* S)

/--
The restriction map `Hⁿ(G,M) ⟶ Hⁿ(H,M)`, defined as a morphism of functors
-/
def rest (n : ℕ) : functor R G n ⟶ Rep.res φ ⋙ functor R S n  where
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

lemma rest_comp (n : ℕ) : rest (φ.comp ψ) n = rest φ (R := R) n ≫ (𝟙 (res φ) ◫ rest ψ n) := by
  ext M : 2
  rw [rest_app]
  simp only [functor_obj, Functor.comp_obj, Functor.id_hcomp, NatTrans.comp_app,
      Functor.whiskerLeft_app, rest_app]
  rw [←map_comp]
  rfl


/--
Given any short exact sewuence `0 → A → B → C → 0` in `Rep R G` and any
subgroup `H` of `G`, the following diagram is commutative

  Hⁿ(G,C) ⟶ H^{n+1}(G A)
      |         |
      ↓         ↓
  Hⁿ(H,C) ⟶ H^{n+1}(G A).

The vertical arrows are restriction and the horizontals are connecting homomorphisms.

For this, it would be sensible to define restriction as a natural transformation, so that it
automatically commutes with the other maps. This requires us to first define cohomology as a functor.
-/
lemma rest_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    {H : Type u} [Group H] [DecidableEq H] (φ : H →* G) (i j : ℕ) (hij : i + 1 = j) :
    δ hS i j hij ≫ (rest φ j).app S.X₁ = (rest φ i).app S.X₃ ≫ δ ((shortExact_res φ).2 hS) i j hij
    := by
  let C₁ := S.map (cochainsFunctor R G)
  let C₂ := (S.map (res φ)).map (cochainsFunctor R H)
  have ses₁ : C₁.ShortExact := map_cochainsFunctor_shortExact hS
  have ses₂ : C₂.ShortExact := by
    apply map_cochainsFunctor_shortExact
    rwa [shortExact_res]
  let this : C₁ ⟶ C₂ := {
    τ₁ := cochainsMap φ (𝟙 ((res φ).obj S.X₁))
    τ₂ := cochainsMap φ (𝟙 ((res φ).obj S.X₂))
    τ₃ := cochainsMap φ (𝟙 ((res φ).obj S.X₃))
  }
  exact HomologicalComplex.HomologySequence.δ_naturality this ses₁ ses₂ i j hij

noncomputable def resSubtypeRangeIso (M : Rep R G) {H : Type u} [Group H] (f : H →* G) (n : ℕ)
    (hf : Function.Injective f) :
    groupCohomology (M ↓ f.range.subtype) n ≅ groupCohomology (M ↓ f) n where
  hom := groupCohomology.map f.rangeRestrict (𝟙 (M ↓ f)) _
  inv := groupCohomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom
    ⟨by dsimp; exact 𝟙 M.V, by simp [res]⟩ _
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by ext; simp) (by simp [res]) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    refine groupCohomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by simp [res]) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupCohomology

namespace groupHomology

noncomputable def resSubtypeRangeIso (M : Rep R G) {H : Type u} [Group H] (f : H →* G) (n : ℕ)
    (hf : Function.Injective f) :
    groupHomology (M ↓ f.range.subtype) n ≅ groupHomology (M ↓ f) n where
  hom := groupHomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom ⟨𝟙 M.V, by simp [res]⟩ _
  inv := groupHomology.map f.rangeRestrict ⟨𝟙 M.V, by simp [res]⟩ _
  hom_inv_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by ext; simp) (by simp [res]) n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    refine groupHomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by simp [res]) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupHomology

end
