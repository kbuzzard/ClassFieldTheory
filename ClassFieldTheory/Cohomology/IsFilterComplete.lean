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
class IsFilterHasudorff {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  haus' : ∀ x : M, (∀ i, x ∈ F i) → x = 0

-- to replace `IsPrecomplete`
/-- `M` is precomplete with respect to the filtration `M_i ≤ M` if any compatible
sequence `I → M` has a limit in `M`. -/
class IsFilterPrecomplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  prec' : ∀ x : (ι → M), (∀ i j, i ≤ j → x i - x j ∈ F i) → ∃ L : M, ∀ i, x i - L ∈ F i

-- to replace `IsAdicComplete`
/-- `M` is complete with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0` and any compatible
sequence `I → M` has a limit in `M`. -/
@[mk_iff] class IsFilterComplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop
    extends IsFilterHasudorff F, IsFilterPrecomplete F

section
variable {M ι σ : Type*} [AddCommGroup M] [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ)

def Completion.set : Set ((i : ι) → M ⧸ AddSubgroup.ofClass (F i)) :=
  {f | ∀ ⦃i j⦄, i ≤ j →
    QuotientAddGroup.map _ (AddSubgroup.ofClass (F i) ⊔ .ofClass (F j)) (.id M) le_sup_left (f i) =
    QuotientAddGroup.map _ _ (.id M) le_sup_right (f j)}

/-- Completion that works for different classes such as `Module` or `AddCommGroup`. -/
def Completion : Type _ := Completion.set F

namespace Completion

def addSubgroup : AddSubgroup ((i : ι) → M ⧸ AddSubgroup.ofClass (F i)) where
  carrier := set F
  zero_mem' _ _ _ := by simp
  add_mem' ha hb _ _ h := by simpa using congr($(ha h) + $(hb h))
  neg_mem' ha _ _ h := by simpa using congr(-$(ha h))

instance : AddCommGroup (Completion F) := addSubgroup F |>.toAddCommGroup

end Completion

def toCompletion : M →+ Completion F where
  toFun x := ⟨fun _ ↦ x, fun _ _ _ ↦ rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toCompletion_injective_iff_isFilterHausdorff :
    Function.Injective (toCompletion F) ↔ IsFilterHasudorff F :=
  sorry

theorem toCompletion_surjective_iff_isFilterPrecomplete :
    Function.Surjective (toCompletion F) ↔ IsFilterPrecomplete F :=
  sorry

theorem toCompletion_bijective_iff_isFilterComplete :
    Function.Bijective (toCompletion F) ↔ IsFilterComplete F := by
  rw [Function.Bijective, isFilterComplete_iff, toCompletion_injective_iff_isFilterHausdorff,
    toCompletion_surjective_iff_isFilterPrecomplete]

noncomputable def limit [IsFilterComplete F] : Completion F ≃+ M :=
  .symm <| .ofBijective _ <| (toCompletion_bijective_iff_isFilterComplete F).mpr ‹_›

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

end FilterCauchySeq

def Completion.mk : FilterCauchySeq F →+ Completion F where
  toFun f := ⟨fun i ↦ (f.val i), fun _ _ h ↦ QuotientAddGroup.eq_iff_sub_mem.mpr (f.2 h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

end

section
variable {M N σ τ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]
  [AddCommGroup N] [SetLike τ N] [AddSubgroupClass τ N] (F : ℕᵒᵈ →o σ) (G : ℕᵒᵈ →o τ)

open OrderDual

-- We thought for a long time about the minimal assumptions on `ι`, and
-- Kevin posited the axiom that `∀ i, ∀ᶠ j, i ≤ j`, and
-- now we think that the only example of that that we care about would just be `ℕ`.
-- and Kenny thinks that under reasonable assumptions, `ℕ` will just be cofinal in `ι`.
def partialSum : ((i : ℕ) → F (toDual i)) →+ FilterCauchySeq (F ∘ toDual) where
  toFun a := ⟨fun i ↦ ∑ j ∈ Finset.range i, a j, fun i₁ i₂ h ↦ by
    dsimp only
    rw [← Finset.sum_range_add_sum_Ico _ h, sub_mem_comm_iff, add_sub_cancel_left]
    exact sum_mem fun j hj ↦ le_sup_left (α := AddSubgroup M) <|
      F.2 (Finset.mem_Ico.mp hj).1 (a j).2⟩
  map_zero' := by ext; simp; rfl
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]; rfl

namespace IsFilterComplete

noncomputable def sum [IsFilterComplete (F ∘ toDual)] : ((i : ℕ) → F (toDual i)) →+ M :=
  (limit (F ∘ toDual) : _ →+ _).comp <| (Completion.mk (F ∘ toDual)).comp (partialSum F)

theorem sum_sub_mem [IsFilterComplete (F ∘ toDual)] {x : ∀ i, F (toDual i)} {i : ℕ} :
    sum F x - ∑ j ∈ Finset.range i, x j ∈ F i :=
  sorry

variable {F G} (φ : M →+ N) (h : ∀ ⦃i x⦄, x ∈ F i → φ x ∈ G i)

theorem map_sum [IsFilterComplete (F ∘ toDual)] [IsFilterComplete (G ∘ toDual)]
    {x : ∀ i, F (toDual i)} : φ (sum F x) = sum G fun i ↦ ⟨φ (x i), h (x i).2⟩ :=
  sorry

end IsFilterComplete

end
