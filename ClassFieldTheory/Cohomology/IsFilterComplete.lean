/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Completeness with respect to a filtration -/

-- to replace `IsHausdorff`
/-- `M` is Hausdorff with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0`. -/
@[mk_iff] class IsFilterHausdorff {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  haus' : ∀ x : M, (∀ i, x ∈ F i) → x = 0

-- to replace `IsPrecomplete`
/-- `M` is precomplete with respect to the filtration `M_i ≤ M` if any compatible
sequence `I → M` has a limit in `M`. -/
@[mk_iff] class IsFilterPrecomplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  prec' : ∀ x : (ι → M), (∀ i j, i ≤ j → x i - x j ∈ AddSubgroup.ofClass (F i) ⊔ .ofClass (F j)) →
    ∃ L : M, ∀ i, x i - L ∈ F i

-- to replace `IsAdicComplete`
/-- `M` is complete with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0` and any compatible
sequence `I → M` has a limit in `M`. -/
@[mk_iff] class IsFilterComplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop
    extends IsFilterHausdorff F, IsFilterPrecomplete F

section
variable {M ι σ : Type*} [AddCommGroup M] [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ)

theorem Filtration.ext [IsFilterHausdorff F] {x y : M} (h : ∀ i, x - y ∈ F i) : x = y :=
  eq_of_sub_eq_zero <| IsFilterHausdorff.haus' _ h

def Completion.set : Set ((i : ι) → M ⧸ AddSubgroup.ofClass (F i)) :=
  {f | ∀ ⦃i j⦄, i ≤ j →
    QuotientAddGroup.map _ (AddSubgroup.ofClass (F i) ⊔ .ofClass (F j)) (.id M) le_sup_left (f i) =
    QuotientAddGroup.map _ (AddSubgroup.ofClass (F i) ⊔ .ofClass (F j)) (.id M) le_sup_right (f j)}

/-- Completion that works for different classes such as `Module` or `AddCommGroup`. -/
def Completion : Type _ := Completion.set F

namespace Completion

def addSubgroup : AddSubgroup ((i : ι) → M ⧸ AddSubgroup.ofClass (F i)) where
  carrier := set F
  zero_mem' _ _ _ := by simp
  add_mem' ha hb _ _ h := by simpa using congr($(ha h) + $(hb h))
  neg_mem' ha _ _ h := by simpa using congr(-$(ha h))

instance : AddCommGroup (Completion F) := addSubgroup F |>.toAddCommGroup

@[simps!] def coeff (i : ι) : Completion F →+ M ⧸ AddSubgroup.ofClass (F i) where
  toFun f := f.val i
  map_zero' := rfl
  map_add' _ _ := rfl

variable {F} in
@[ext] lemma ext {f g : Completion F} (h : f.val = g.val) : f = g :=
  Subtype.ext h

@[simp] lemma coe_zero : (0 : Completion F).val = 0 := rfl

@[simp] lemma coe_add {f g : Completion F} : (f + g).val = f.val + g.val := rfl

end Completion

@[simps] def toCompletion : M →+ Completion F where
  toFun x := ⟨fun _ ↦ x, fun _ _ _ ↦ rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def FilterCauchySeq.set : Set (ι → M) :=
  {f | ∀ ⦃i j⦄, i ≤ j → f i - f j ∈ AddSubgroup.ofClass (F i) ⊔ .ofClass (F j)}

-- generalises `AdicCompletion.AdicCauchySequence`
/-- An enlargement of `Completion` that surjects to `Completion`. -/
def FilterCauchySeq : Type _ := FilterCauchySeq.set F

namespace FilterCauchySeq

@[ext] lemma ext {a b : FilterCauchySeq F} (h : a.val = b.val) : a = b :=
  Subtype.ext h

def addSubgroup : AddSubgroup (ι → M) where
  carrier := set F
  zero_mem' _ _ _ := by simp
  add_mem' ha hb _ _ h := by simp_rw [Pi.add_apply, add_sub_add_comm]; exact add_mem (ha h) (hb h)
  neg_mem' ha _ _ h := by simp_rw [Pi.neg_apply]; rw [neg_sub_neg, ← neg_sub]; exact neg_mem (ha h)

instance : AddCommGroup (FilterCauchySeq F) := addSubgroup F |>.toAddCommGroup

variable {F} in
/-- A constructor that is intended for when `F` is antitone. -/
@[simps!] def mk (x : ι → M) (hx : ∀ ⦃i j⦄, i ≤ j → x i - x j ∈ F i) : FilterCauchySeq F :=
  ⟨x, fun _ _ hij ↦ le_sup_left (α := AddSubgroup M) <| hx hij⟩

end FilterCauchySeq

@[simps!] def Completion.mk : FilterCauchySeq F →+ Completion F where
  toFun f := ⟨fun i ↦ (f.val i), fun _ _ h ↦ QuotientAddGroup.eq_iff_sub_mem.mpr (f.2 h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable {F}

theorem Completion.mk_surjective : (⇑(Completion.mk F)).Surjective := fun x ↦ by
  refine ⟨⟨fun i ↦ (x.val i).out, fun i j h ↦ ?_⟩, by ext; simp⟩
  have := x.2 h
  simp only
  generalize x.val i = xi at *
  generalize x.val j = xj at *
  cases xi using QuotientAddGroup.induction_on with | H xi =>
  cases xj using QuotientAddGroup.induction_on with | H xj =>
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  change (xi : M ⧸ (_ : AddSubgroup M)) = xj at this
  convert this using 1 <;> rw [QuotientAddGroup.eq_iff_sub_mem]
  · refine le_sup_left (α := AddSubgroup M) ?_
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq']
  · refine le_sup_right (α := AddSubgroup M) ?_
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq']

theorem toCompletion_injective_iff_isFilterHausdorff :
    Function.Injective (toCompletion F) ↔ IsFilterHausdorff F := by
  rw [isFilterHausdorff_iff, injective_iff_map_eq_zero]
  simp_rw [Completion.ext_iff, funext_iff, toCompletion_apply_coe, Completion.coe_zero,
    Pi.zero_apply, QuotientAddGroup.eq_zero_iff, ← SetLike.mem_coe, AddSubgroup.coe_ofClass]

theorem toCompletion_surjective_iff_isFilterPrecomplete :
    Function.Surjective (toCompletion F) ↔ IsFilterPrecomplete F := by
  rw [isFilterPrecomplete_iff, Function.Surjective, Completion.mk_surjective.forall]
  simp_rw [Completion.ext_iff, funext_iff, toCompletion_apply_coe, Completion.mk_apply_coe,
    eq_comm (b := QuotientAddGroup.mk <| (_ : FilterCauchySeq F).val _),
    QuotientAddGroup.eq_iff_sub_mem]
  exact ⟨fun H x hx ↦ H ⟨x, hx⟩, fun H x ↦ H x.1 x.2⟩

theorem toCompletion_bijective_iff_isFilterComplete :
    Function.Bijective (toCompletion F) ↔ IsFilterComplete F := by
  rw [Function.Bijective, isFilterComplete_iff, toCompletion_injective_iff_isFilterHausdorff,
    toCompletion_surjective_iff_isFilterPrecomplete]

variable (F)

noncomputable def limit [IsFilterComplete F] : Completion F ≃+ M :=
  .symm <| .ofBijective _ <| toCompletion_bijective_iff_isFilterComplete.mpr ‹_›

end

open OrderDual

section Antitone
variable {M ι σ : Type*} [AddCommGroup M] [Preorder ι] [SetLike σ M] [AddSubgroupClass σ M]
  {F : ιᵒᵈ →o σ}

theorem FilterCauchySeq.mk_surjective (y : FilterCauchySeq (F ∘ toDual)) :
    ∃ x hx, .mk x hx = y :=
  ⟨y.val, fun _ _ hij ↦ sup_le (α := AddSubgroup M) le_rfl (F.2 hij) (y.2 hij), rfl⟩

theorem limit_sub_mem [IsFilterComplete (⇑F ∘ ⇑toDual)] (x : FilterCauchySeq (F ∘ toDual)) {i : ι} :
    limit _ (.mk _ x) - x.val i ∈ F (toDual i) := by
  generalize hxy : limit _ (.mk _ x) = y
  rw [← AddEquiv.eq_symm_apply] at hxy
  exact QuotientAddGroup.eq_iff_sub_mem.mp congr(($hxy.symm).val i)

end Antitone


section
variable {M N σ τ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]
  [AddCommGroup N] [SetLike τ N] [AddSubgroupClass τ N] (F : ℕᵒᵈ →o σ) (G : ℕᵒᵈ →o τ)

-- We thought for a long time about the minimal assumptions on `ι`, and
-- Kevin posited the axiom that `∀ i, ∀ᶠ j, i ≤ j`, and
-- now we think that the only example of that that we care about would just be `ℕ`.
-- and Kenny thinks that under reasonable assumptions, `ℕ` will just be cofinal in `ι`.
def partialSum : ((i : ℕ) → F (toDual i)) →+ FilterCauchySeq (F ∘ toDual) where
  toFun a := .mk (fun i ↦ ∑ j ∈ Finset.range i, a j) fun i₁ i₂ h ↦ by
    dsimp only
    rw [← Finset.sum_range_add_sum_Ico _ h, sub_mem_comm_iff, add_sub_cancel_left]
    exact sum_mem fun j hj ↦ F.2 (Finset.mem_Ico.mp hj).1 (a j).2
  map_zero' := by ext; simp; rfl
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]; rfl

namespace IsFilterComplete

noncomputable def sum [IsFilterComplete (F ∘ toDual)] : ((i : ℕ) → F (toDual i)) →+ M :=
  (limit (F ∘ toDual) : _ →+ _).comp <| (Completion.mk (F ∘ toDual)).comp (partialSum F)

theorem sum_sub_mem [IsFilterComplete (F ∘ toDual)] {x : ∀ i, F (toDual i)} {i : ℕ} :
    sum F x - ∑ j ∈ Finset.range i, x j ∈ F (toDual i) :=
  limit_sub_mem ..

variable {F G} {Φ : Type*} [FunLike Φ M N] [AddMonoidHomClass Φ M N] {φ : Φ}
  (h : ∀ ⦃i x⦄, x ∈ F i → φ x ∈ G i)

/-- A "continuous" map commutes with infinite "sum". -/
theorem map_sum [IsFilterComplete (F ∘ toDual)] [IsFilterComplete (G ∘ toDual)]
    {x : ∀ i, F (toDual i)} : φ (sum F x) = sum G fun i ↦ ⟨φ (x i), h (x i).2⟩ := by
  refine Filtration.ext (G ∘ toDual) fun i ↦ ?_
  have h₁ := h <| sum_sub_mem (x := x) (i := i)
  have h₂ := sum_sub_mem (x := fun i ↦ ⟨φ (x i), h (x i).2⟩) (i := i)
  rw [map_sub, _root_.map_sum] at h₁
  convert sub_mem h₁ h₂ using 1
  exact (sub_sub_sub_cancel_right ..).symm

end IsFilterComplete

end
