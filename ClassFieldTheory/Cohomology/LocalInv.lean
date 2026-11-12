/-
Copyright (c) 2025 Yaël Dillies, Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Aaron Liu
-/
module

public import ClassFieldTheory.Cohomology.FiniteCyclic.UpDown
public import ClassFieldTheory.Mathlib.GroupTheory.Torsion
public import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The local invariant

In this file, we define the carry cocycle, show that it is a two-cocycle and generates
`H²(ℤ/nℤ, ℤ)` (with the trivial `ℤ/nℤ`-action on `ℤ`). In turn, this lets us define the local
invariant as the isomorphism `H²(ℤ/nℤ, ℤ) ≅ ℤ/nℤ`.
-/

@[expose] public noncomputable section

open groupCohomology TateCohomology CategoryTheory Limits

local notation3:1024 M:1024 "ᵐ" => Multiplicative M

namespace groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

@[simp] lemma shortComplexH2_moduleCatToCycles_apply (x : G → A) (g : G × G) :
    DFunLike.coe (F := cocycles₂ A) ((shortComplexH2 A).moduleCatToCycles x) g =
      (d₁₂ A).hom x g :=
  rfl

variable {A} in
lemma H2Iso_inv_hom_mk (f : cocycles₂ A) :
    (H2Iso A).inv.hom (Submodule.Quotient.mk f) = (H2π A).hom f := by
  rw [← Submodule.mkQ_apply, ← H2π_comp_H2Iso_hom_apply, Iso.hom_inv_id_apply]

end groupCohomology

variable {n : ℕ}

/-- The carry cocycle. -/
def carry (i j : ZMod n) : ℤ := (i.cast + j.cast - (i + j).cast) / n

lemma carry_eq_ite [NeZero n] (i j : ZMod n) : carry i j = if n ≤ i.val + j.val then 1 else 0 := by
  zify
  simp only [carry, ZMod.cast_add_eq_ite, ZMod.natCast_val]
  split_ifs
  · rw [sub_sub_cancel, Int.ediv_self (NeZero.ne _)]
  · rw [sub_self, Int.zero_ediv]

lemma carry_comm (i j : ZMod n) : carry i j = carry j i := by simp [carry, add_comm]

lemma carry_neg_one_one (hn : 2 ≤ n) : carry (-1 : ZMod n) 1 = 1 := by
  obtain _ | _ | n := n
  · simp at *
  · simp at *
  · rw [carry_eq_ite, ZMod.val_neg_one, ZMod.val_one'' (by omega)]
    simp

lemma carry_one_right_of_ne_neg_one [NeZero n] {i : ZMod n} (hi : i ≠ -1) : carry i 1 = 0 := by
  obtain _ | _ | n := n
  · simp at *
  · cases hi <| Subsingleton.elim (α := ZMod 1) ..
  simp [carry_eq_ite, ZMod.val_one'']
  have := (ZMod.val_injective _).ne hi
  rw [ZMod.val_neg_one] at this
  have := i.val_lt
  omega

lemma carry_add_carry_add_left (i j k : ZMod n) :
     carry i j + carry (i + j) k = (i.cast + j.cast + k.cast - (i + j + k).cast) / n := by
  obtain rfl | h := eq_zero_or_neZero n
  · simp [carry]
  rw [carry, carry,
    ← Int.add_ediv_of_dvd_left <| by simp [← ZMod.intCast_zmod_eq_zero_iff_dvd]]
  congr 1
  ring

lemma carry_add_carry_add_right (i j k : ZMod n) :
    carry j k + carry i (j + k) = (i.cast + j.cast + k.cast - (i + j + k).cast) / n := by
  rw [carry_comm i, carry_add_carry_add_left, ← add_rotate, ← add_rotate i]

variable (n) in
/-- The carry cocycle as a two-cocycle. -/
def carryCocycle : cocycles₂ (.trivial ℤ (ZMod n)ᵐ ℤ) where
  val ij := carry ij.1.toAdd ij.2.toAdd
  property := by
    simp only [mem_cocycles₂_def,  Representation.isTrivial_def, LinearMap.id_coe, id_eq,
      toAdd_mul, add_comm, Multiplicative.forall, toAdd_ofAdd, sub_eq_iff_eq_add, add_zero, ←
      add_sub_assoc]
    rintro i j k
    rw [carry_add_carry_add_right, ← carry_add_carry_add_left]

@[simp] lemma carryCocycle_apply (i j : Multiplicative <| ZMod n) :
    carryCocycle n (i, j) = carry i.toAdd j.toAdd := rfl

variable [NeZero n]

/-- The local invariant as a map from two-cocycles. -/
def localInvAuxAux : cocycles₂ (.trivial ℤ (ZMod n)ᵐ ℤ) →+ ZMod n where
  toFun f := ∑ i : ZMod n, Int.cast (f (.ofAdd i, .ofAdd 1))
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

variable (n) in
private lemma localInvAuxAux_carryCocycle : localInvAuxAux (carryCocycle n) = 1 := by
  obtain rfl | hn₁ := eq_or_ne n 1
  · exact Subsingleton.elim ..
  have := NeZero.ne n
  dsimp [localInvAuxAux]
  rw [Fintype.sum_eq_single (-1 : ZMod n) (by simp +contextual [carry_one_right_of_ne_neg_one]),
    carry_neg_one_one (by omega)]
  simp

variable (n) in
lemma range_le_ker_localInvAuxAux :
    (shortComplexH2 (.trivial ℤ (ZMod n)ᵐ ℤ)).moduleCatToCycles.range.toAddSubgroup ≤
      (localInvAuxAux (n := n)).ker := by
  rintro _ ⟨x, rfl⟩
  simpa [localInvAuxAux, Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_add_eq_sub,
    sub_eq_zero]
    using (Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) fun i ↦ (x (.ofAdd i) : ZMod n)).symm

open CategoryTheory in
variable (n) in
/-- The local invariant. -/
def localInvAux : H2 (.trivial ℤ (ZMod n)ᵐ ℤ) →+ ZMod n := by
  refine .comp ?_ (H2Iso _).hom.hom.toAddMonoidHom
  refine QuotientAddGroup.lift _ localInvAuxAux ?_
  exact range_le_ker_localInvAuxAux n

private lemma localInvAux_apply (x : H2 (.trivial ℤ (ZMod n)ᵐ ℤ)) :
    localInvAux n x = QuotientAddGroup.lift _ localInvAuxAux (range_le_ker_localInvAuxAux n)
      ((H2Iso _).hom.hom x) := rfl

private lemma localInvAux_H2π_hom (f : cocycles₂ (.trivial ℤ (ZMod n)ᵐ ℤ)) :
    localInvAux n ((H2π _).hom f) = localInvAuxAux f := by
  rw [localInvAux_apply, H2π_comp_H2Iso_hom_apply, Submodule.mkQ_apply,
    ← Submodule.Quotient.quotientAddGroupMk_eq_mk, QuotientAddGroup.lift_mk]

/-- Multiplying the fundamental class by `i`. Auxiliary definition for `carryH2`. -/
def carryH2Aux (i : ZMod n) : H2 (.trivial ℤ (ZMod n)ᵐ ℤ) :=
  i.val • (H2Iso _).inv.hom (QuotientAddGroup.mk (carryCocycle n))

/-- By a computation, `localInvAux n ∘ carryH2Aux = id`. -/
lemma rightInverse_carryH2Aux_localInvAux : carryH2Aux.RightInverse (localInvAux n) := by
  intro i
  rw [carryH2Aux, map_nsmul, Submodule.Quotient.quotientAddGroupMk_eq_mk, H2Iso_inv_hom_mk,
    localInvAux_H2π_hom, localInvAuxAux_carryCocycle]
  simp

/-- Since `|H²(ℤ/nℤ, ℤ)| = |ℤ/nℤ|` and `localInvAux n ∘ carryH2Aux = id`, we also have
`carryH2Aux ∘ localInvAux n = id`. -/
lemma leftInverse_carryH2Aux_localInvAux : carryH2Aux.LeftInverse (localInvAux n) := by
  have e : H2 (.trivial ℤ (ZMod n)ᵐ ℤ) ≃ (ZMod n)ᵐ :=
    (groupCohomology.evenTrivialInt (by simp) _ even_two).toLinearEquiv.toEquiv
  have : Finite (H2 <| .trivial ℤ (ZMod n)ᵐ ℤ) := .of_equiv (ZMod n)ᵐ e.symm
  have : Fintype (H2 <| .trivial ℤ (ZMod n)ᵐ ℤ) := .ofFinite _
  refine rightInverse_carryH2Aux_localInvAux.leftInverse_of_card_le ?_
  simp [Fintype.card_congr e]

variable (n)

/-- `ℤ` as a trivial `ℤ/nℤ`-module has second cohomology group `ℤ/nℤ`, with the forward map given by
the local invariant.

See `groupCohomology.evenTrivialInt` for the basis-free computation in the case of a trivial
torsion-free representation of a finite cyclic group. -/
def localInv : H2 (.trivial ℤ (ZMod n)ᵐ ℤ) ≃+ ZMod n where
  toFun := localInvAux n
  invFun := carryH2Aux
  left_inv := leftInverse_carryH2Aux_localInvAux
  right_inv := rightInverse_carryH2Aux_localInvAux
  map_add' := by simp

@[simp] lemma localInv_H2π_hom (f : cocycles₂ (.trivial ℤ (ZMod n)ᵐ ℤ)) :
    localInv n ((H2π _).hom f) = ∑ i : ZMod n, Int.cast (f (.ofAdd i, .ofAdd 1)) := by
  rw [localInv, AddEquiv.coe_mk, Equiv.coe_fn_mk, localInvAux_H2π_hom]
  simp [localInvAuxAux]

@[simp] lemma localInv_symm_apply (i : ZMod n) :
    (localInv n).symm i = i.val • (H2Iso _).inv.hom (QuotientAddGroup.mk (carryCocycle n)) := rfl

/-- `ℤ` as a trivial `ℤ/nℤ`-module has second cohomology group `ℤ/nℤ`, with the forward map given by
the local invariant. `localInv` as an isomorphism in `ModuleCat ℤ`.

See `groupCohomology.evenTrivialInt` for the basis-free computation in the case of a trivial
torsion-free representation of a finite cyclic group. -/
@[simps!]
def localInvIso : H2 (.trivial ℤ (ZMod n)ᵐ ℤ) ≅ .of ℤ (ZMod n) :=
  (localInv n).toIntLinearEquiv.toModuleIso
