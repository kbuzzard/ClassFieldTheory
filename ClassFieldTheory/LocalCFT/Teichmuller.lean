/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ClassFieldTheory.LocalCFT.NonArchDef

/-! # Teichmüller character

Given complete discrete valuation ring `(R,m,k)` with finite residue field `k`, we define
Teichmüller character `k →* R` (a monoid homomorphism, i.e. preserves only multiplication).

... but we don't have CDVR so we will just do it for local fields.
-/

section Lemmas

theorem Filter.HasBasis.comp_dense {β ι ι' : Type*} [Preorder ι]
    {F : Filter β} {p : ι → Prop} {p' : ι' → Prop} {g : ι → Set β} (b : F.HasBasis p g)
    (hg : Antitone g) (f : ι' → ι) (hp : ∀ ⦃i'⦄, p' i' → p (f i'))
    (dense : ∀ ⦃i⦄, p i → ∃ i', p' i' ∧ i ≤ f i') :
    F.HasBasis p' (g ∘ f) := by
  refine ⟨fun t ↦ ?_⟩
  rw [b.mem_iff]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ?_, by aesop⟩
  obtain ⟨i', hi'1, hi'2⟩ := dense hi1
  exact ⟨i', hi'1, (hg hi'2).trans hi2⟩

theorem Filter.HasBasis.comp_dense' {β ι ι' : Type*} [Preorder ι]
    {F : Filter β} {p : ι → Prop} {p' : ι' → Prop} {g : ι → Set β} (b : F.HasBasis p g)
    (hg : Monotone g) (f : ι' → ι) (hp : ∀ ⦃i'⦄, p' i' → p (f i'))
    (dense : ∀ ⦃i⦄, p i → ∃ i', p' i' ∧ f i' ≤ i) :
    F.HasBasis p' (g ∘ f) := by
  refine ⟨fun t ↦ ?_⟩
  rw [b.mem_iff]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ?_, by aesop⟩
  obtain ⟨i', hi'1, hi'2⟩ := dense hi1
  exact ⟨i', hi'1, (hg hi'2).trans hi2⟩

namespace WithZero

theorem exp_surj' {M : Type*} {y : Mᵐ⁰} (hy : y ≠ 0) :
    ∃ x, exp x = y := by
  cases y <;> tauto

theorem exp_zero' {M : Type*} [Zero M] : exp (0 : M) = 1 := rfl

theorem exp_le_exp' {M : Type*} [LE M] {x y : M} : exp x ≤ exp y ↔ x ≤ y := WithZero.coe_le_coe

@[simp] theorem exp_le_one_iff {M : Type*} [LE M] [Zero M] {x : M} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero' (M := M) ▸ exp_le_exp'

@[simp] theorem one_le_exp_iff {M : Type*} [LE M] [Zero M] {x : M} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero' (M := M) ▸ exp_le_exp'

theorem lt_exp_iff {x : ℤᵐ⁰} {n : ℤ} : x < exp n ↔ x ≤ exp (n - 1) := by
  cases x
  · simp
  · simp [-exp_sub, Int.le_sub_one_iff]

end WithZero

namespace OrderMonoidIso

variable {α β : Type*} [Preorder α] [Preorder β] [Mul α] [Mul β] (e : α ≃*o β)

nonrec theorem surjective : (⇑e).Surjective :=
  e.surjective

@[simp] theorem le_symm_apply {x y} : x ≤ e.symm y ↔ e x ≤ y :=
  e.toOrderIso.le_symm_apply

@[simp] theorem symm_apply_le {x y} : e.symm x ≤ y ↔ x ≤ e y :=
  e.toOrderIso.symm_apply_le

@[simp] theorem lt_symm_apply {x y} : x < e.symm y ↔ e x < y :=
  e.toOrderIso.lt_symm_apply

@[simp] theorem symm_apply_lt {x y} : e.symm x < y ↔ x < e y :=
  e.toOrderIso.symm_apply_lt

end OrderMonoidIso

@[simp] theorem Valuation.algebraMap_integer_coe {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) :
    ⇑(algebraMap v.integer R) = (↑) :=
  rfl

instance IsUniformAddGroup.addSubgroupClass {α S : Type*} [UniformSpace α] [AddGroup α]
    [SetLike S α] [AddSubgroupClass S α] [IsUniformAddGroup α] (s : S) :
    IsUniformAddGroup s :=
  AddSubgroup.isUniformAddGroup <| .ofClass s

protected theorem Commute.add_pow_prime_pow_eq'
    {R : Type*} [Semiring R] {p : ℕ} (hp : Nat.Prime p) {x y : R} (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * ∑ k ∈ Finset.Ioo 0 (p ^ n),
      x ^ (k - 1) * y ^ (p ^ n - k - 1) * ((p ^ n).choose k / p :) := by
  rw [h.add_pow_prime_pow_eq hp]
  congr 1
  simp_rw [mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_Ioo] at hi
  rw [h.left_comm, ← mul_assoc x, ← pow_succ', (h.symm.pow_right _).left_comm, ← mul_assoc y,
    ← pow_succ', Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]

theorem add_pow_prime_pow_eq'
    {R : Type*} [CommSemiring R] {p : ℕ} (hp : Nat.Prime p) (x y : R) (n : ℕ) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * ∑ k ∈ Finset.Ioo 0 (p ^ n),
      x ^ (k - 1) * y ^ (p ^ n - k - 1) * ((p ^ n).choose k / p :) :=
  (Commute.all x y).add_pow_prime_pow_eq' hp _

theorem exists_add_pow_prime_pow_eq'
    {R : Type*} [CommSemiring R] {p : ℕ} (hp : Nat.Prime p) (x y : R) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  ⟨_, add_pow_prime_pow_eq' hp x y n⟩

theorem CharP.mem {R : Type*} [CommRing R] (p : ℕ) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp <| by simp

theorem FiniteField.pow_natCard {K : Type*} [GroupWithZero K] [Finite K] (a : K) :
    a ^ Nat.card K = a := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, pow_card]

namespace IsValuativeTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

open ValuativeRel


end IsValuativeTopology

end Lemmas



namespace IsNonarchimedeanLocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K]

section TopologicalSpace
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem map_irreducible {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K ϖ = (valueGroupWithZeroIsoInt K).symm (.exp (-1)) :=
  (OrderMonoidIso.eq_symm_apply _).mpr <| valueGroupWithZeroIsoInt_irreducible hϖ

theorem mem_maximalIdeal_pow_iff {x : 𝒪[K]} {n : ℕ} :
    x ∈ 𝓂[K] ^ n ↔ valuation K x ≤ (valueGroupWithZeroIsoInt K).symm (.exp (-n)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← Valuation.Integers.le_iff_dvd (Valuation.integer.integers _),
    map_pow, map_pow, Valuation.algebraMap_integer_coe, map_irreducible hϖ, ← map_pow,
    ← WithZero.exp_nsmul]
  simp

variable (K) in
theorem hasBasis_nhds : (nhds (0 : K)).HasBasis (fun _n : ℕ ↦ True)
    fun n ↦ {p | valuation K p < (valueGroupWithZeroIsoInt K).symm (.exp (-n))} :=
  (IsValuativeTopology.hasBasis_nhds_zero' K).comp_dense'
    (fun _ _ h₁ _ h₂ ↦ h₂.trans_le h₁)
    _ (by aesop) <| by
  refine (valueGroupWithZeroIsoInt K).symm.surjective.forall.mpr fun x hx ↦ ?_
  rw [map_ne_zero] at hx
  obtain ⟨x, rfl⟩ := WithZero.exp_surj' hx
  obtain ⟨n, rfl | rfl⟩ := x.eq_nat_or_neg
  · exact ⟨0, by simp⟩
  · aesop

variable (K) in
theorem hasBasis_nhds_integer : (nhds (0 : 𝒪[K])).HasBasis (fun _n : ℕ ↦ True)
    fun n ↦ {p | p ∈ 𝓂[K] ^ (n + 1)} := by
  convert (hasBasis_nhds K).comap Subtype.val using 1
  · exact nhds_subtype ..
  ext n x
  simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.preimage_setOf_eq, Set.mem_setOf_eq]
  rw [mem_maximalIdeal_pow_iff, OrderMonoidIso.lt_symm_apply, WithZero.lt_exp_iff,
    OrderMonoidIso.le_symm_apply, Nat.cast_succ]
  ring_nf

theorem isClosed_closedBall' (x : 𝒪[K]) (n : ℕ) :
    IsClosed {y | y - x ∈ 𝓂[K] ^ n} := by
  convert (IsValuativeTopology.isClosed_closedBall
    ((valueGroupWithZeroIsoInt K).symm (.exp (-n)))).preimage_val.preimage
      (continuous_sub_right x) using 1
  ext y
  simp [mem_maximalIdeal_pow_iff]

/-- The sequence `x ^ q ^ n` that defines the Teichmuller character. -/
@[simps] noncomputable def teichmullerSeq : 𝒪[K] →* (ℕ → 𝒪[K]) where
  toFun x n := x ^ Nat.card 𝓀[K] ^ n
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_pow]

-- a lemma to prove that `teichmullerSeq` is Cauchy
theorem pow_sub_pow_mem {a b : 𝒪[K]} {i : ℕ} (hi : i ≠ 0) (h : a - b ∈ 𝓂[K] ^ i) :
    a ^ Nat.card 𝓀[K] - b ^ Nat.card 𝓀[K] ∈ 𝓂[K] ^ (i + 1) := by
  have h₁ : 1 ≤ i := by grind
  let := Fintype.ofFinite 𝓀[K]
  obtain ⟨p, hCp, ⟨n, hn₀⟩, hp, hn : _ = _ ^ n⟩ := FiniteField.card' 𝓀[K]
  have h₂ : 2 ≤ p ^ n := Nat.succ_le.mpr <| one_lt_pow' hp.one_lt hn₀.ne'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq' hp (a - b) b n
  rw [Nat.card_eq_fintype_card, hn, show a = a - b + b by abel, hr, add_right_comm,
    add_sub_cancel_right, mul_assoc _ b]
  refine add_mem ?_ ?_
  · have := Ideal.pow_mem_pow h (p ^ (n : ℕ))
    rw [← pow_mul] at this
    exact Ideal.pow_le_pow_right (add_one_le_two_mul h₁ |>.trans
      (mul_comm i 2 ▸ mul_right_mono h₂)) this
  · rw [pow_succ']
    have : CharP (𝒪[K] ⧸ IsLocalRing.maximalIdeal 𝒪[K]) p := hCp
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (CharP.mem _ _) h)

-- another lemma
theorem pow_card_sub_mem (x : 𝒪[K]) : x ^ Nat.card 𝓀[K] - x ∈ 𝓂[K] := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
  change algebraMap _ 𝓀[K] x ^ Nat.card 𝓀[K] - algebraMap _ 𝓀[K] x = 0
  rw [FiniteField.pow_natCard, sub_self]

theorem teichmullerSeq_succ_sub_mem (x : 𝒪[K]) (i : ℕ) :
    teichmullerSeq x (i + 1) - teichmullerSeq x i ∈ 𝓂[K] ^ (i + 1) := by
  induction i with
  | zero =>
    simp_rw [teichmullerSeq_apply, zero_add, pow_zero, pow_one]
    exact pow_card_sub_mem x
  | succ i ih =>
    convert pow_sub_pow_mem _ ih using 2 <;> simp [teichmullerSeq, pow_succ, pow_mul]

theorem teichmullerSeq_add_sub_mem (x : 𝒪[K]) (n i : ℕ) :
    teichmullerSeq x (n + i) - teichmullerSeq x n ∈ 𝓂[K] ^ (n + 1) := by
  rw [show teichmullerSeq x n = teichmullerSeq x (n + 0) by simp,
    ← Finset.sum_range_sub (teichmullerSeq x <| n + ·) i]
  refine sum_mem fun j hj ↦ ?_
  exact Ideal.pow_le_pow_right (by rw [Nat.add_eq]; omega) <| teichmullerSeq_succ_sub_mem x _

theorem teichmullerSeq_sub_teichmullerSeq_mem {x y : 𝒪[K]} (h : x - y ∈ 𝓂[K]) (n : ℕ) :
    teichmullerSeq x n - teichmullerSeq y n ∈ 𝓂[K] ^ (n + 1) := by
  induction n with
  | zero => simpa [teichmullerSeq] using h
  | succ n ih =>
    simp_rw [teichmullerSeq_apply, pow_succ _ n, pow_mul, ← teichmullerSeq_apply]
    exact pow_sub_pow_mem (by omega) ih

end TopologicalSpace

section UniformSpace
variable [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

variable (K) in
theorem hasBasis_uniformity : (uniformity 𝒪[K]).HasBasis (fun _n : ℕ ↦ True)
    fun n ↦ {p | p.1 - p.2 ∈ 𝓂[K] ^ (n + 1)} :=
  .uniformity_of_nhds_zero_swapped <| hasBasis_nhds_integer K

theorem cauchySeq_iff' (a : ℕ → 𝒪[K]) :
    CauchySeq a ↔ ∀ i : ℕ, ∃ N, ∀ n ≥ N, a n - a N ∈ 𝓂[K] ^ (i + 1) := by
  convert (hasBasis_uniformity K).cauchySeq_iff' (β := ℕ); simp

theorem cauchySeq_iff (a : ℕ → 𝒪[K]) :
    CauchySeq a ↔ ∀ i : ℕ, ∃ N, ∀ n ≥ N, a n - a N ∈ 𝓂[K] ^ i := by
  rw [cauchySeq_iff']
  refine ⟨fun h i ↦ ?_, by aesop⟩
  obtain _ | i := i
  · simp
  · exact h i

-- special case
theorem cauchySeq_of_succ {a : ℕ → 𝒪[K]} (ha : ∀ i, a (i + 1) - a i ∈ 𝓂[K] ^ (i + 1)) :
    CauchySeq a := by
  refine (cauchySeq_iff' a).mpr fun i ↦ ⟨i, fun n hn ↦ ?_⟩
  obtain ⟨n, rfl⟩ := le_iff_exists_add.mp hn
  rw [show a i = a (i + 0) by simp, ← Finset.sum_range_sub (a <| i + ·) n]
  refine sum_mem fun c _ ↦ ?_
  exact Ideal.pow_le_pow_right (by rw [Nat.add_eq]; omega) <| ha _

theorem cauchySeq_teichmuller (x : 𝒪[K]) : CauchySeq (teichmullerSeq x) :=
  cauchySeq_of_succ fun i ↦ teichmullerSeq_succ_sub_mem x i

end UniformSpace

section TopologicalSpace
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem limUnder_teichmullerSeq_mem (x : 𝒪[K]) (n : ℕ) :
    limUnder .atTop (teichmullerSeq x) - teichmullerSeq x n ∈ 𝓂[K] ^ (n + 1) := by
  refine IsClosed.mem_of_frequently_of_tendsto (f := teichmullerSeq x) (b := .atTop)
    (s := {y | y - teichmullerSeq x n ∈ IsLocalRing.maximalIdeal ↥𝒪[K] ^ (n + 1)})
    (isClosed_closedBall' _ _) ?_ ?_
  · rw [Filter.frequently_atTop]
    refine fun i ↦ ⟨n+i, i.le_add_left n, teichmullerSeq_add_sub_mem x n i⟩
  · letI := IsTopologicalAddGroup.toUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    exact (cauchySeq_teichmuller x).tendsto_limUnder

theorem ext_maximalIdeal {x y : 𝒪[K]} (h : ∀ n, x - y ∈ 𝓂[K] ^ n) : x = y :=
  sub_eq_zero.mp <| Ideal.mem_bot.mp <| Ideal.iInf_pow_eq_bot_of_isDomain 𝓂[K]
    (Ideal.IsMaximal.ne_top inferInstance) ▸ Ideal.mem_iInf.mpr h

theorem ext_maximalIdeal' {x y : 𝒪[K]} (h : ∀ n, x - y ∈ 𝓂[K] ^ (n + 1)) : x = y :=
  ext_maximalIdeal fun n ↦ n.casesOn (by simp) h

/-- The Teichmüller character `𝓀[K] →* 𝒪[K]`. -/
noncomputable def teichmuller' : 𝓀[K] →* 𝒪[K] where
  toFun x := Quotient.liftOn x (limUnder .atTop <| teichmullerSeq ·) fun x₁ x₂ hx ↦ by
    refine ext_maximalIdeal' fun n ↦ ?_
    have h₁ := limUnder_teichmullerSeq_mem x₁ n
    have h₂ := limUnder_teichmullerSeq_mem x₂ n
    have h₃ := teichmullerSeq_sub_teichmullerSeq_mem ((Submodule.quotientRel_def _).mp hx) n
    have := add_mem (sub_mem h₁ h₂) h₃
    ring_nf at this ⊢
    exact this
  map_one' := Filter.Tendsto.limUnder_eq <| by simp [Pi.one_def]
  map_mul' x y := Quotient.inductionOn₂ x y fun x y ↦ by
    letI := IsTopologicalAddGroup.toUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    change limUnder _ _ = limUnder _ _ * limUnder _ _
    rw [map_mul]
    exact Filter.Tendsto.limUnder_eq <| .mul
      (cauchySeq_teichmuller x).tendsto_limUnder (cauchySeq_teichmuller y).tendsto_limUnder

end TopologicalSpace

end IsNonarchimedeanLocalField
