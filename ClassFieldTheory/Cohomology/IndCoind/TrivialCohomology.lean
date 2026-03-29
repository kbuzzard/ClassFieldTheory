/-
Copyright (c) 2025 Yaël Dillies, Nailin Guan, Gareth Ma, Arend Mellendijk, Yannis Monbru,
Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Nailin Guan, Gareth Ma, Arend Mellendijk, Yannis Monbru, Michał Mrugała
-/
module

public import ClassFieldTheory.Cohomology.IndCoind.Finite
public import ClassFieldTheory.Cohomology.TrivialCohomology
public import ClassFieldTheory.Mathlib.LinearAlgebra.Finsupp.Defs
public import ClassFieldTheory.Mathlib.RepresentationTheory.Rep
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# (Co)induced modules have trivial (co)homology

Let `G` be a group. We prove that `coind₁.obj A` has trivial cohomology and `ind₁.obj A` has trivial
homology.
We prove that `ind₁'.obj M` is isomorphic to `(ind₁ G).obj M.V`, and therefore has trivial homology.
Similarly we show that `coind₁'.obj M` is isomorphic to `(coind₁ G).obj M.V` and therefore has
trivial cohomology. In the case that `G` is a finite group, we show that all four of these
representations have trivial Tate cohomology.
-/

@[expose] public noncomputable section

open
  Finsupp
  Function
  Rep
  CategoryTheory
  groupHomology
  groupCohomology

section FINDMEINMATHLIB
variable {G : Type*} [Group G] {H : Subgroup G}

lemma bijective_out_mul : Bijective fun ((h, y) : H × G ⧸ H) ↦ y.out * h where
  left := by
    rintro ⟨h₁, y₁⟩ ⟨h₂, y₂⟩ h₁₂
    obtain rfl : y₁ = y₂ := by simpa using congr((QuotientGroup.mk $h₁₂ : G ⧸ H))
    simpa using h₁₂
  right y := by
    obtain ⟨h, hyh⟩ := QuotientGroup.mk_out_eq_mul H y
    exact ⟨(h⁻¹, QuotientGroup.mk y), by simp [hyh]⟩

@[simps!]
def prodQuotEquiv (H : Subgroup G) : H × G ⧸ H ≃ G := .ofBijective _ bijective_out_mul

end FINDMEINMATHLIB

universe u

variable {R G A : Type u} [CommRing R] [Group G] {M : Rep.{u} R G} {A : ModuleCat.{u} R}

namespace Rep

def resInd₁AsFinsuppLinearEquiv (H : Subgroup G) : (G →₀ A) ≃ₗ[R] (H →₀ (G ⧸ H →₀ A)) :=
  open scoped Classical in
  (Finsupp.domLCongr (prodQuotEquiv H).symm).trans (Finsupp.curryLinearEquiv R)

def resCoind₁AsPiLinearEquiv (H : Subgroup G) : (G → A) ≃ₗ[R] (H → G ⧸ H → A) :=
  .trans (.funCongrLeft _ _ <| prodQuotEquiv H) (.curry R ..)

@[simp]
lemma resInd₁AsFinsuppLinearEquiv_apply (H : Subgroup G) (f : G →₀ A) (h : H) (x : G ⧸ H) :
    resInd₁AsFinsuppLinearEquiv H f h x = f (x.out * h) := by
  simp [resInd₁AsFinsuppLinearEquiv, prodQuotEquiv]

@[simp]
lemma resCoind₁AsPiLinearEquiv_apply (H : Subgroup G) (f : G → A) (h : H) (x : G ⧸ H) :
    resCoind₁AsPiLinearEquiv H f h x = f (x.out * h) := rfl

def resInd₁AsFinsuppIso (H : Subgroup G) :
    ind₁AsFinsupp G A ↓ H.subtype ≅ ind₁AsFinsupp H (.of R <| G ⧸ H →₀ A) :=
  Rep.mkIso <| .mk (resInd₁AsFinsuppLinearEquiv H) fun g ↦ by
    classical
    ext; simp [Finsupp.single_apply, mul_inv_eq_iff_eq_mul, mul_assoc]

def resCoind₁AsPiIso (H : Subgroup G) :
    coind₁AsPi G A ↓ H.subtype ≅ coind₁AsPi H (.of R <| G ⧸ H → A) :=
  Rep.mkIso <| .mk (resCoind₁AsPiLinearEquiv H) fun g ↦ by ext; simp [mul_assoc]

instance trivialHomology_ind₁AsFinsupp : TrivialHomology (ind₁AsFinsupp.{u, u, u} G A) := by
  classical
  -- Let `H` be a subgroup of `G`.
  refine ⟨fun H n ↦ ?_⟩
  -- The restriction to `H` of `ind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `ind₁^H (G ⧸ H →₀ A)`.
  -- By Shapiro's lemma, this has trivial homology.
  exact isZero_of_trivialHomology.of_iso <| ((groupHomology.functor _ _ _).mapIso <|
    (resInd₁AsFinsuppIso H) ≪≫ (ind₁AsFinsuppIso _)) ≪≫ (indIso ..)

instance trivialCohomology_coind₁AsPi : TrivialCohomology (coind₁AsPi G A) := by
  classical
  -- Let `H` be a subgroup of `G`.
  refine ⟨fun H n ↦ ?_⟩
  -- The restriction to `H` of `coind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `coind₁^H (G ⧸ H → A)`.
  -- By Shapiro's lemma, this has trivial cohomology.
  exact isZero_of_trivialCohomology.of_iso  <| ((groupCohomology.functor _ _ _).mapIso <|
    (resCoind₁AsPiIso H).trans (coind₁AsPiIso _)).trans (groupCohomology.coindIso ..)

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

instance trivialHomology_coind₁AsPi : TrivialHomology (coind₁AsPi G A) :=
  .of_iso (coind₁AsPiIso _)

set_option backward.isDefEq.respectTransparency false in
/-- `coind₁` considered as the concrete left-regular action on `G →₀ A` has trivial Tate cohomology.
-/
instance trivialTateCohomology_coind₁AsPi : TrivialTateCohomology (Rep.coind₁AsPi G A) := by
  classical
  refine .of_cases fun H ↦ ?_
  -- Let's collect some trivialities.
  letI : Fintype G := .ofFinite _
  letI : Fintype H := .ofFinite _
  letI : Fintype (G ⧸ H) := @Fintype.ofFinite _ Subgroup.finite_quotient_of_finiteIndex
  have aux (f : G → A) (x : G) :
      ∑ y : G ⧸ H, ∑ h : H, (if x * h = y.out then f (y.out * (↑h)⁻¹) else 0) = f x := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', ← Fintype.sum_ite_eq x f]
    refine Fintype.sum_equiv (.trans (.prodCongrLeft fun _ ↦ .inv _) <| prodQuotEquiv H) _ _ ?_
    rintro ⟨h, y⟩
    simp [eq_mul_inv_iff_mul_eq]
  refine ⟨.of_iso ?_ <| TateCohomology.zeroIso _, .of_iso ?_ <| TateCohomology.negOneIso _⟩
  · -- First, let's prove the 0-th cohomology group is trivial.
    simp only [res_obj_V, res_obj_ρ, Representation.norm, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Function.comp_apply, ModuleCat.isZero_of_iff_subsingleton,
      Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf_eq_top, SetLike.le_def,
      Representation.mem_invariants, funext_iff, Representation.coind₁AsPi_apply, Subtype.forall,
      LinearMap.mem_range, LinearMap.coe_sum, Finset.sum_apply]
    intro f hf
    -- Assume we have such `f`.
    -- We claim we can take `g := ∑ y : G ⧸ H, Pi.single y.out (f y.out)`, where `out` is an
    -- arbitrary section `G ⧸ H → G`.
    refine ⟨∑ y : G ⧸ H, Pi.single y.out (f y.out), fun x ↦ ?_⟩
    -- This is true because, when evaluated at a point `x`, the sum has exactly one non-zero term,
    -- which turns out to be exactly `f x`.
    rw [← aux f x]
    conv_lhs => simp +contextual only [Finset.sum_apply, Pi.single_apply,
      eq_comm (a := _ * _), SetLike.coe_mem, hf]
    simp only [← Subgroup.coe_inv]
    simp +contextual [Finset.sum_comm (α := H) (s := Finset.univ), eq_comm (b := Quotient.out _),
      mul_assoc, ← Subgroup.coe_mul H, -Subgroup.coe_inv, -InvMemClass.coe_inv]
  · -- Second, let's prove the -1-st cohomology group is trivial.
    simp only [res_obj_V, res_obj_ρ, Representation.norm, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Function.comp_apply, ModuleCat.isZero_of_iff_subsingleton,
      Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf_eq_top, SetLike.le_def,
      LinearMap.mem_ker, LinearMap.coe_sum, Finset.sum_apply, funext_iff,
      Representation.coind₁AsPi_apply, Pi.ofNat_apply]
    -- This is equivalent to...
    -- change ∀ f : G → A, (∀ x, ∑ h : H, f (x * h) = 0) → f ∈ Representation.Coinvariants.ker _
    -- Assume we have such `f`.
    intro f hf
    replace hf x : ∑ h : H, f (x * (↑h)⁻¹) = 0 := by
      rw [← hf x]; exact Fintype.sum_equiv (.inv _) _ _ (by simp)
    -- Then `f` is equal to the sum of `f (y.out * h⁻¹) * (1_{y.out * h⁻¹} - 1_{y.out}`
    -- over `y : G ⧸ H, h : H`, where `out : G ⧸ H → G` is an arbitrary section.
    have key :
        f =
          ∑ y : G ⧸ H, ∑ h : H,
            (Pi.single (y.out * h⁻¹) (f (y.out * h⁻¹)) -
              Pi.single y.out (f (y.out * h⁻¹))) := by
      ext; simp [Pi.single_apply, eq_mul_inv_iff_mul_eq, aux, hf]
    rw [key]
    -- Now we are done, since each summand is in the kernel of the coinvariants by definition.
    refine Submodule.sum_mem _ fun y _ ↦ Submodule.sum_mem _ fun h _ ↦ ?_
    convert Representation.Coinvariants.sub_mem_ker h
      (Pi.single y.out (f (y.out * h⁻¹)) : G → A)
    ext
    simp [Pi.single_apply, eq_mul_inv_iff_mul_eq]

instance trivialTateCohomology_coind₁ : TrivialTateCohomology ((coind₁ G).obj A) :=
  .of_iso (coind₁AsPiIso A).symm

instance trivialTateCohomology_ind₁ : TrivialTateCohomology ((ind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A)

instance trivialTateCohomology_ind₁' : TrivialTateCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialTateCohomology_coind₁' : TrivialTateCohomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

/--
The `H`-invariants of `(coind₁ G).obj A` form an representation of `G ⧸ H` with trivial cohomology.
-/
instance coind₁_quotientToInvariants_trivialCohomology (A : ModuleCat R) {Q : Type u} [Group Q]
    {φ : G →* Q} (surj : Function.Surjective φ) :
    ((coind₁ G ⋙ quotientToInvariantsFunctor' surj).obj A).TrivialCohomology :=
  .of_iso (Rep.coind₁_quotientToInvariants_iso A surj)

instance coind₁'_quotientToInvariants_trivialCohomology {Q : Type u} [Group Q] {φ : G →* Q}
    (surj : Function.Surjective φ) : ((coind₁'.obj M) ↑ surj).TrivialCohomology := by
  have iso := (quotientToInvariantsFunctor' surj).mapIso (coind₁'_obj_iso_coind₁ M)
  have : ((quotientToInvariantsFunctor' surj).obj ((coind₁ G).obj
    (ModuleCat.of R M.V))).TrivialCohomology :=
    coind₁_quotientToInvariants_trivialCohomology _ _
  exact .of_iso iso

end Rep
