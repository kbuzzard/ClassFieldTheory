/-
Copyright (c) 2025 Yaël Dillies, Nailin Guan, Arend Mellendijk, Gareth Ma, Yannis Monbru,
Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Nailin Guan, Arend Mellendijk, Gareth Ma, Yannis Monbru, Michał Mrugała
-/
import ClassFieldTheory.GroupCohomology._05_TrivialCohomology
import ClassFieldTheory.GroupCohomology._07_coind1_and_ind1
import ClassFieldTheory.Mathlib.Algebra.Category.ModuleCat.Basic
import ClassFieldTheory.Mathlib.Algebra.Module.Submodule.Range
import ClassFieldTheory.Mathlib.LinearAlgebra.Finsupp.Defs
import ClassFieldTheory.Mathlib.RepresentationTheory.Rep

/-!
# (Co)induced modules have trivial (co)homology

Let `G` be a group. We prove that `coind₁.obj A` has trivial cohomology and `ind₁.obj A` has trivial
homology.
We prove that `ind₁'.obj M` is isomorphic to `(ind₁ G).obj M.V`, and therefore has trivial homology.
Similarly we show that `coind₁'.obj M` is isomorphic to `(coind₁ G).obj M.V` and therefore has
trivial cohomology. In the case that `G` is a finite group, we show that all four of these
representations have trivial Tate cohomology.
-/

open
  Finsupp
  Representation
  Rep
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupHomology
  groupCohomology


noncomputable section

variable {R G S A : Type} [CommRing R] [Group G] [Group S] {M : Rep R G} {A : ModuleCat R}

namespace Rep

@[simps snd]
/- a coset decomposition of x, acording -/
def cosetDec (φ : S →* G) (sec : G ⧸ φ.range → G) (secSpec : ∀ x, QuotientGroup.mk (sec x) = x)
    (x : G) : S × (G ⧸ φ.range) := by
  refine ⟨ ?_, (QuotientGroup.mk x)⟩
  let x' : G := sec (QuotientGroup.mk x : G ⧸ φ.range)
  let y : G := x'⁻¹ * x
  have : y ∈ φ.range := by
    apply QuotientGroup.leftRel_apply.mp
    exact Quotient.eq''.mp (secSpec ↑x)
  exact Classical.choose <| MonoidHom.mem_range.1 this

lemma cosetDecSpec {S : Type} [Group S] (φ : S →* G) (sec : G ⧸ φ.range → G)
    (secSpec : ∀ x, QuotientGroup.mk (sec x) = x) (x : G) :
    sec (cosetDec φ sec secSpec x).2 * φ (cosetDec φ sec secSpec x).1 = x := by
  apply mul_eq_of_eq_inv_mul
  -- Lean does not infer the motive by itself
  let p := fun z => (φ z = (sec ↑x)⁻¹ * x)
  apply @Classical.choose_spec _ p

lemma cosetDec_inj {S : Type} [Group S] (φ : S →* G) (sec : G ⧸ φ.range → G)
    (inj : Function.Injective φ) (secSpec : ∀ x, QuotientGroup.mk (sec x) = x ) (s : S)
    (r : G ⧸ φ.range) :
    cosetDec φ sec secSpec (sec r * φ s) = (s, r) := by
  have eq2 : (cosetDec φ sec secSpec (sec r * φ s)).2 = r := by
    calc
    _ = QuotientGroup.mk (sec r * φ s) := by simp [secSpec]
    _ = r := by simp [secSpec]
  have := cosetDecSpec φ sec secSpec (sec r * φ s)
  simp only [eq2, mul_right_inj] at this
  ext
  · exact inj this
  · exact eq2

@[simps]
def prodQuotEquiv {φ : S →* G} (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (sec_spec : ∀ g, sec g = g) :  S × G ⧸ φ.range ≃ G where
  toFun p := sec p.2 * φ p.1
  invFun h := cosetDec φ sec sec_spec h
  left_inv p := by simp only [cosetDec_inj, hφ]
  right_inv h := by simp [-Rep.cosetDec_snd, cosetDecSpec]

def resInd₁AsFinsuppModuleIso  (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    (G →₀ A) ≃ₗ[R] (S →₀ (G ⧸ φ.range →₀ A)) :=
  open scoped Classical in
  (Finsupp.domLCongr (prodQuotEquiv hφ sec hsec).symm).trans (Finsupp.finsuppProdLEquiv R)

def resCoind₁AsPiModuleIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) : (G → A) ≃ₗ[R] (S → G ⧸ φ.range → A) :=
  .trans (.funCongrLeft _ _ <| prodQuotEquiv hφ sec hsec) (.curry R ..)

@[simp]
theorem resInd₁AsFinsuppModuleIso_apply {φ : S →* G} (hφ : Function.Injective φ)
    (sec : G ⧸ φ.range → G) (hsec : ∀ g, sec g = g) (f : G →₀ A) (s : S) (h : G ⧸ φ.range) :
    (resInd₁AsFinsuppModuleIso φ hφ sec hsec f s h) = f (sec h * φ s) := by
  simp [resInd₁AsFinsuppModuleIso, prodQuotEquiv]

@[simp]
theorem resCoind₁AsPiModuleIso_apply {φ : S →* G} (hφ : Function.Injective φ)
    (sec : G ⧸ φ.range → G) (hsec : ∀ g, sec g = g) (f : G → A) (s : S) (h : G ⧸ φ.range) :
    resCoind₁AsPiModuleIso φ hφ sec hsec f s h = f (sec h * φ s) := rfl

def resInd₁AsFinsuppIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    ind₁AsFinsupp G A ↓ φ ≅ ind₁AsFinsupp S (.of R <| G ⧸ φ.range →₀ A) := by
  refine Rep.mkIso _ _ (resInd₁AsFinsuppModuleIso φ hφ sec hsec).toModuleIso ?_
  rintro g f
  simp
  ext s h
  simp only [resInd₁AsFinsuppModuleIso_apply]
  erw [ind₁AsFinsupp_ρ (G := S) (A := .of R (G ⧸ φ.range →₀ A)) (g := g), res_ρ_apply,
    ind₁AsFinsupp_ρ, coe_mapDomainLinearEquiv, coe_mapDomainLinearEquiv]
  simp [resInd₁AsFinsuppModuleIso, mul_assoc]

def resCoind₁AsPiIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    coind₁AsPi G A ↓ φ ≅ coind₁AsPi S (.of R <| G ⧸ φ.range → A) := by
  refine Rep.mkIso _ _ (resCoind₁AsPiModuleIso φ hφ sec hsec).toModuleIso ?_
  rintro g f
  simp
  ext s h
  simp [resCoind₁AsPiModuleIso_apply]
  erw [coind₁AsPi_ρ, coind₁AsPi_ρ, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap]
  simp [resCoind₁AsPiModuleIso, mul_assoc]

instance trivialHomology_ind₁AsFinsupp : TrivialHomology (ind₁AsFinsupp G A) := by
  classical
  -- Let `S` be a subgroup of `G`.
  refine ⟨fun S _ φ hφ n ↦ ?_⟩
  -- The restriction to `S` of `ind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `ind₁^S (G ⧸ S →₀ A)`.
  -- By Shapiro's lemma, this has trivial homology.
  exact (isZero_of_trivialHomology ..).of_iso  <| ((groupHomology.functor _ _ _).mapIso <|
    (resInd₁AsFinsuppIso φ hφ Quotient.out (by simp)).trans (ind₁AsFinsuppIso _)).trans (indIso ..)

instance trivialCohomology_coind₁AsPi : TrivialCohomology (coind₁AsPi G A) := by
  classical
  -- Let `S` be a subgroup of `G`.
  refine ⟨fun S _ φ hφ n ↦ ?_⟩
  -- The restriction to `S` of `coind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `coind₁^S (G ⧸ S → A)`.
  -- By Shapiro's lemma, this has trivial cohomology.
  exact (isZero_of_trivialCohomology ..).of_iso  <| ((groupCohomology.functor _ _ _).mapIso <|
    (resCoind₁AsPiIso φ hφ Quotient.out (by simp)).trans (coind₁AsPiIso _)).trans
      (groupCohomology.coindIso ..)

instance trivialHomology_ind₁ (A : ModuleCat R) : TrivialHomology ((ind₁ G).obj A) :=
  .of_iso (ind₁AsFinsuppIso _).symm

instance trivialCohomology_coind₁ (A : ModuleCat R) : TrivialCohomology ((coind₁ G).obj A) :=
  .of_iso (coind₁AsPiIso _).symm

instance trivialHomology_ind₁' : (ind₁'.obj M).TrivialHomology :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialCohomology_coind₁' : (coind₁'.obj M).TrivialCohomology :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

variable [Finite G]

instance trivialCohomology_ind₁ : TrivialCohomology ((ind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A)

instance trivialHomology_coind₁ : TrivialHomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance trivialCohomology_ind₁' : TrivialCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialHomology_coind₁' : TrivialCohomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

instance trivialCohomology_ind₁AsFinsupp : TrivialCohomology (ind₁AsFinsupp G A) :=
  .of_iso (ind₁AsFinsuppIso _)

instance trivialTateCohomology_ind₁AsFinsupp : TrivialTateCohomology (ind₁AsFinsupp G A) := by
    refine .of_cases ?_
    rintro H _ _ φ hφ
    have := Finite.of_injective φ hφ
    have : (ind₁AsFinsupp G A ↓ φ) ≅ ind₁AsFinsupp H (.of R <| G ⧸ φ.range →₀ A) :=
      resInd₁AsFinsuppIso φ hφ Quotient.out (fun g ↦ QuotientGroup.out_eq' g)
    dsimp
    constructor
    · --refine IsZero.of_iso ?_ ((TateCohomology 0).mapIso this)
      refine IsZero.of_iso ?_ (TateCohomology_zero_iso _)
      simp [Submodule.subsingleton_quotient_iff_eq_top]
      rw [SetLike.le_def]
      rintro f hf
      have : Finite <| G ⧸ φ.range := Subgroup.finite_quotient_of_finiteIndex
      have : Fintype <| G ⧸ φ.range := Fintype.ofFinite _
      use ∑ x : G ⧸ φ.range, single (Quotient.out x) (f (Quotient.out x))
      ext g
      simp [Representation.norm]
      rw [← Finset.sum_comm]
      simp_rw [Finsupp.coe_finset_sum, Finset.sum_apply]
      calc ∑ g : G ⧸ S, ∑ s : S, (fun₀ | g.out * s => f g.out) x
        _ = ∑ g : G ⧸ S, ∑ s : S, if g.out * s = x then f g.out else 0 := by
          simp only [Finsupp.single_apply]
        _ = ∑ g : G ⧸ S, ∑ s : S, if s = g.out⁻¹ * x then f g.out else 0 := by
          apply Finset.sum_congr rfl fun _ _ ↦ ?_
          apply Finset.sum_congr rfl fun _ _ ↦ ?_
          congr 1
          simp [eq_inv_mul_iff_mul_eq]
        _ = ∑ g : G ⧸ S, ∑ s ∈ (Finset.univ : Finset S).map ⟨S.subtype, S.subtype_injective⟩, if s = g.out⁻¹ * x then f g.out else 0 := by
          simp_rw [Finset.sum_map]
          simp
        _ = ∑ g : G ⧸ S, ∑ s ∈ (Finset.univ : Finset G).filter (· ∈ S), if s = g.out⁻¹ * x then f g.out else 0 := by
          apply Finset.sum_congr rfl fun _ _ ↦ ?_
          apply Finset.sum_congr ?_ fun _ _ ↦ rfl
          ext w
          simp
        _ = ∑ g : G ⧸ S, ∑ s : G, if s = g.out⁻¹ * x then if s ∈ S then f g.out else 0 else 0 := by
          simp_rw [Finset.sum_filter, ← ite_and, and_comm]
        _ = ∑ g : G ⧸ S, if g.out⁻¹ * x ∈ S then f g.out else 0 := by
          simp
        _ = ∑ g : G ⧸ S, if g = ⟦x⟧ then f g.out else 0 := by
          simp [h₁]
        _ = f x := by
          simp
          convert hf x ⟨_, h₀' S x⟩
          simp
    · sorry

instance trivialTateCohomology_ind₁ : TrivialTateCohomology ((ind₁ G).obj A) := by
    refine .of_cases ?_
    rintro H _ _ φ hφ
    have : (ind₁ G).obj A ↓ φ ≅ ind₁AsFinsupp H (.of R <| G ⧸ φ.range →₀ A) := sorry
    constructor
    · sorry
    · sorry

instance trivialTateCohomology_coind₁ : TrivialTateCohomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance trivialTateCohomology_ind₁' : TrivialTateCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialTateCohomology_coind₁' : TrivialTateCohomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

/--
The `H`-invariants of `(coind₁ G).obj A` form an representation of `G ⧸ H` with trivial cohomology.
-/
instance coind₁_quotientToInvariants_trivialCohomology (A : ModuleCat R) {Q : Type} [Group Q]
    {φ : G →* Q} (surj : Function.Surjective φ) :
    ((coind₁ G ⋙ quotientToInvariantsFunctor surj).obj A).TrivialCohomology :=
  .of_iso (Rep.coind₁_quotientToInvariants_iso A surj)

instance coind₁'_quotientToInvariants_trivialCohomology {Q : Type} [Group Q] {φ : G →* Q}
    (surj : Function.Surjective φ) : ((coind₁'.obj M) ↑ surj).TrivialCohomology := by
  have iso := (quotientToInvariantsFunctor surj).mapIso (coind₁'_obj_iso_coind₁ M)
  have _ : ((quotientToInvariantsFunctor surj).obj ((coind₁ G).obj M.V)).TrivialCohomology
  · exact coind₁_quotientToInvariants_trivialCohomology M.V surj
  exact .of_iso iso

end Rep
