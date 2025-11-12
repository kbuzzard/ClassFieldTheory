import Mathlib
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic

variable (K L M: Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]

--def IsCompositum : Prop := sorry
  -- exists L₁ →ₐ[K] M and L₂ →ₐ[K] M
  -- such that L1 and L2 as `IntermediateField K M`
  -- have sup = top

open TensorProduct
example : Nontrivial (L ⊗[K] M) := inferInstance

example : Nonempty (MaximalSpectrum (L ⊗[K] M)) := inferInstance

noncomputable section

def Compositum := L ⊗[K] M ⧸ (Ideal.exists_maximal (L ⊗[K] M)).choose
  deriving Algebra L, Algebra K, IsScalarTower K L

noncomputable instance : Field (Compositum K L M) :=
  @Ideal.Quotient.field (L ⊗[K] M) _ _  (Ideal.exists_maximal (L ⊗[K] M)).choose_spec

--noncomputable def bad_algebra_instance : Algebra M (Compositum K L M) :=

open Polynomial in
instance (f : K[X]) [IsSplittingField K M f] :
    IsSplittingField L (Compositum K L M) (f.map (algebraMap K L) : L[X]) :=
  sorry

instance [Module.Finite K M] : Module.Finite L (Compositum K L M) := by
  unfold Compositum
  infer_instance

-- TODO remove finiteness
instance [Module.Finite K M] [Normal K M] : Normal L (Compositum K L M) := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField K M
  exact .of_isSplittingField (p.map (algebraMap K L))

def Compositum.algebraMap : M →ₐ[K] Compositum K L M :=
    letI : Algebra M (L ⊗[K] M):= Algebra.TensorProduct.rightAlgebra
    Algebra.algHom K M (_ ⧸ _)

class IsCompositum (K L M N) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    (f : M →ₐ[K] N) : Prop where
  sup_eq_top :
    ((Algebra.algHom K L N).fieldRange : IntermediateField K N) ⊔
    (f.fieldRange : IntermediateField K N) = ⊤

set_option synthInstance.maxHeartbeats 100000 in
theorem Compositum.isCompositum :
    IsCompositum K L M (Compositum K L M) (Compositum.algebraMap K L M) := by
  letI : Field (Compositum K L M) := inferInstance
  letI : Field (L ⊗[K] M ⧸ (Ideal.exists_maximal (L ⊗[K] M)).choose) :=
    @Ideal.Quotient.field (L ⊗[K] M) _ _  (Ideal.exists_maximal (L ⊗[K] M)).choose_spec
  constructor
  -- The sup of the two field ranges should equal ⊤
  apply le_antisymm le_top
  -- Show that every element is in the sup
  intro x
  -- Every element x of Compositum comes from the tensor product
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- We'll show this element is in the sup by induction on the tensor product structure
  induction t using TensorProduct.induction_on with
  | zero =>
    intro _
    change (Ideal.Quotient.mk _  0 : Compositum K L M) ∈ _
    rw [map_zero]
    exact @IntermediateField.zero_mem K (Compositum K L M) _ _ _ _
  | tmul l m =>
    intro _
    change (Ideal.Quotient.mk _ (l ⊗ₜ m) : Compositum K L M) ∈ _
    -- The key is that l ⊗ₜ m = (l ⊗ₜ 1) * (1 ⊗ₜ m) in the tensor product
    have h_eq : l ⊗ₜ m = (l ⊗ₜ[K] (1:M)) * ((1:L) ⊗ₜ m) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h_eq, map_mul]
    -- It suffices to show each factor is in the respective field range
    refine IntermediateField.mul_mem _ ?_ ?_
    · -- l ⊗ₜ 1 is in the L field range
      change (Ideal.Quotient.mk _ (l ⊗ₜ 1) : Compositum K L M) ∈ _
      sorry
    · -- 1 ⊗ₜ m is in the M field range via Compositum.algebraMap
      change (Ideal.Quotient.mk _ (1 ⊗ₜ m) : Compositum K L M) ∈ _
      sorry
  | add x y hx hy =>
    simp at hx hy
    simp
    exact IntermediateField.add_mem _ hx hy
