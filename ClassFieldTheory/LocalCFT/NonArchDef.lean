import ClassFieldTheory.LocalCFT.Continuity
import ClassFieldTheory.Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib

/-!
# Definition of Non-Archimedean Local Fields

We define non-archimedean local fields as a class `IsNonArchLF`.

-/

/-
-- in mathlib now!
class IsNonarchimedeanLocalField (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] : Prop extends
  IsValuativeTopology K,
  IsUniformAddGroup K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K
  -- ValuativeRel.IsRankLeOne K -- TODO: in future mathlib
  -- IsTopologicalDivisionRing K,
  -- CompleteSpace K,
  -- ValuativeRel.IsDiscrete K
-/

open ValuativeRel

namespace IsNonarchimedeanLocalField

section Padic

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonarchimedeanLocalField ℚ_[p] where
  mem_nhds_iff := sorry

end Padic

section TopologicalSpace
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

example : IsTopologicalDivisionRing K := inferInstance
example : ValuativeRel.IsRankLeOne K := inferInstance
example : IsDiscreteValuationRing 𝒪[K] := inferInstance
example : CompactSpace 𝒪[K] := inferInstance
example : Finite 𝓀[K] := inferInstance

instance : T2Space K :=
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  open scoped Valued in inferInstance

theorem prime_ringChar : (ringChar 𝓀[K]).Prime :=
  CharP.char_is_prime 𝓀[K] _

/-- This is how you show that there is a uniformiser (which in Mathlib is called `Irreducible`). -/
example : ∃ ϖ : 𝒪[K], Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible _

example : ∀ ϖ : 𝒪[K], Irreducible ϖ → ϖ ≠ 0 :=
  fun _ h ↦ h.ne_zero

lemma associated_iff_of_irreducible (x y : 𝒪[K]) (hx : Irreducible x) :
    Associated y x ↔ Irreducible y :=
  ⟨fun hyx ↦ hyx.symm.irreducible hx,
  fun hy ↦ IsDiscreteValuationRing.associated_of_irreducible _ hy hx⟩

def compactOpenOK : TopologicalSpace.CompactOpens K where
  carrier := 𝒪[K]
  isCompact' := isCompact_iff_compactSpace.mpr <| inferInstanceAs (CompactSpace 𝒪[K])
  isOpen' := IsValuativeTopology.isOpen_closedBall (R := K) one_ne_zero

noncomputable def equivResidueField : 𝓀[K] ≃ₐ[𝒪[K]] 𝓂[K].ResidueField :=
  .ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField _)

instance : Finite 𝓂[K].ResidueField := .of_equiv 𝓀[K] <| equivResidueField K

-- TODO: add Haar measure (or check that it works with `example`)

section RankOne
-- # Tools to make a rank one instance

open NNReal WithZero

/-- A chosen valuation to `ℝ≥0` that sends any uniformiser to the given `ε`. -/
noncomputable def valuationOfIoo (ε : Set.Ioo (0 : ℝ) 1) : Valuation K ℝ≥0 := by
  refine (valuation K).map ((WithZeroMulInt.toNNReal (e := ⟨1/ε, ?_⟩) ?_).comp
    (valueGroupWithZeroIsoInt K)) ?_
  · exact one_div_nonneg.mpr ε.2.1.le
  · exact coe_ne_zero.mp <| one_div_ne_zero ε.2.1.ne'
  · simp only [MonoidWithZeroHom.coe_comp]
    refine (WithZeroMulInt.toNNReal_strictMono ?_).monotone.comp
      (OrderMonoidIso.strictMono _).monotone
    exact coe_lt_coe.mp <| one_lt_one_div ε.2.1 ε.2.2

@[elab_as_elim, induction_eliminator, cases_eliminator]
def _root_.WithZero.expRecOn {M : Type*} {motive : Mᵐ⁰ → Sort*} (x : Mᵐ⁰)
    (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) : motive x :=
  Option.recOn x zero exp

@[simp] lemma _root_.WithZero.expRecOn_zero {M : Type*} {motive : Mᵐ⁰ → Sort*}
    (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) :
    @WithZero.expRecOn M motive 0 zero exp = zero := rfl

@[simp] lemma _root_.WithZero.expRecOn_exp {M : Type*} {motive : Mᵐ⁰ → Sort*}
    (x : M) (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) :
    @WithZero.expRecOn M motive (.exp x) zero exp = exp x := rfl

@[simp] lemma _root_.WithZero.exp_lt_one_iff {M : Type*} [Preorder M] [Zero M] {x : M} :
    WithZero.exp x < 1 ↔ x < 0 :=
  WithZero.exp_lt_exp

/-- The characterisation of `exp (-1) : ℤᵐ⁰`. -/
theorem _root_.WithZero.exp_neg_one_def {x : ℤᵐ⁰} :
    x = .exp (-1) ↔ x < 1 ∧ ∀ y < 1, y ≤ x := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl
    refine ⟨by decide, fun y hy ↦ y.expRecOn (by decide) (fun y hy ↦ ?_) hy⟩
    rw [exp_lt_one_iff] at hy
    rw [exp_le_exp]
    linarith
  · cases x
    · exact absurd (h.2 (exp (-1)) (by decide)) (by decide)
    · refine le_antisymm ?_ (h.2 _ (by decide))
      rw [exp_lt_one_iff] at h
      rw [exp_le_exp]
      linarith

@[simp] lemma _root_.map_lt_one_iff {F α β : Type*} [Preorder α] [Preorder β]
    [MulOneClass α] [MulOneClass β] [EquivLike F α β] [OrderIsoClass F α β] [MulEquivClass F α β]
    (f : F) {x : α} : f x < 1 ↔ x < 1 :=
  map_one f ▸ map_lt_map_iff f

lemma _root_.Valuation.Integers.associated_iff_eq {F Γ₀ O : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}
    [CommRing O] [Algebra O F] (hv : v.Integers O) {x y : O} :
    Associated x y ↔ v (algebraMap O F x) = v (algebraMap O F y) := by
  have := hv.hom_inj.isDomain
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, hv.le_iff_dvd, hv.le_iff_dvd, and_comm]

variable {K}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem le_valuation_irreducible_of_lt_one {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x} (hx : x < 1) : x ≤ valuation K ϖ := by
  obtain ⟨x, rfl⟩ := valuation_surjective x
  lift x to 𝒪[K] using hx.le
  obtain h₁ | h₁ := ValuationRing.dvd_total x ϖ
  · obtain h₂ | h₂ := hϖ.dvd_iff.mp h₁
    · exact absurd ((Valuation.integer.integers (valuation K)).one_of_isUnit h₂) (ne_of_lt hx)
    · rw [(Valuation.integer.integers (valuation K)).associated_iff_eq] at h₂
      exact h₂.ge
  · exact (Valuation.integer.integers (valuation K)).le_of_dvd h₁

theorem valueGroupWithZeroIsoInt_irreducible {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valueGroupWithZeroIsoInt K (valuation K ϖ) = .exp (-1) := by
  rw [exp_neg_one_def]
  simpa [(valueGroupWithZeroIsoInt K).surjective.forall] using
    ⟨Valuation.integer.v_irreducible_lt_one hϖ, fun _ ↦ le_valuation_irreducible_of_lt_one hϖ⟩

@[simp] lemma WithZeroMulInt.toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) {n : ℤ} :
    WithZeroMulInt.toNNReal he (.exp n) = e ^ n := by
  simp [WithZeroMulInt.toNNReal]

theorem valuationOfIoo_irreducible {ε : Set.Ioo (0 : ℝ) 1} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    (valuationOfIoo K ε ϖ : ℝ) = ε := by
  simp [valuationOfIoo, valueGroupWithZeroIsoInt_irreducible hϖ]

variable (K)

noncomputable def rankOneOfIoo (ε : Set.Ioo (0 : ℝ) 1) : (valuation K).RankOne := by
  refine
  { hom := ((WithZeroMulInt.toNNReal (e := ⟨1/ε, ?_⟩) ?_).comp
      (valueGroupWithZeroIsoInt K))
    strictMono' := (WithZeroMulInt.toNNReal_strictMono ?_).comp (OrderMonoidIso.strictMono _) }
  · exact one_div_nonneg.mpr ε.2.1.le
  · exact coe_ne_zero.mp <| one_div_ne_zero ε.2.1.ne'
  · exact coe_lt_coe.mp <| one_lt_one_div ε.2.1 ε.2.2

noncomputable def inhabitedIoo : Inhabited (Set.Ioo (0 : ℝ) 1) := ⟨0.67, by norm_num, by norm_num⟩
attribute [local instance] inhabitedIoo

noncomputable example : (valuation K).RankOne := rankOneOfIoo K default

theorem _root_.Valuation.ext_lt_one {F Γ₀ : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] {v₁ v₂ : Valuation F Γ₀} (equiv : v₁.IsEquiv v₂)
    (h : ∀ ⦃x⦄, v₁ x < 1 → v₁ x = v₂ x) : v₁ = v₂ := by
  ext x
  obtain hx1 | hx1 | h1x := lt_trichotomy (v₁ x) 1
  · exact h hx1
  · rw [hx1, eq_comm]
    exact equiv.eq_one_iff_eq_one.mp hx1
  · refine inv_injective ?_
    rw [← map_inv₀, ← map_inv₀]
    refine h ?_
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1x

theorem valuation_ext {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v₁ v₂ : Valuation K Γ₀}
    [v₁.Compatible] [v₂.Compatible] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (h : v₁ ϖ = v₂ ϖ) : v₁ = v₂ := by
  refine Valuation.ext_lt_one (ValuativeRel.isEquiv _ _) fun x hx ↦ ?_
  by_cases hx₀ : x = 0
  · simp [hx₀]
  have := (ValuativeRel.isEquiv v₁ (valuation K)).lt_one_iff_lt_one.mp hx
  lift x to 𝒪[K] using this.le
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (Subtype.coe_ne_coe.mp hx₀) hϖ
  have := (Valuation.Integers.associated_iff_eq (Valuation.integer.integers (valuation K))).mp hn
  have h₁ := (ValuativeRel.isEquiv v₁ (valuation K)).val_eq.mpr this
  have h₂ := (ValuativeRel.isEquiv v₂ (valuation K)).val_eq.mpr this
  refine h₁.trans <| Eq.trans ?_ h₂.symm
  simp_rw [map_pow]
  exact congr($h ^ n)

end RankOne

end TopologicalSpace

section UniformSpace
variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

example : CompleteSpace 𝒪[K] := inferInstance
example : CompleteSpace K := inferInstance
-- example : ProperSpace K := inferInstance

end UniformSpace

section extension_of_local_fields
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

variable [Algebra K L] [ValuativeExtension K L]
-- Andrew proved that `ValuativeExtension K L` is automatic.

-- TODO: MOVE
theorem _root_.Irreducible.ne_zero'
    {K S : Type*} [MonoidWithZero K] [SetLike S K] [SubmonoidClass S K]
    {s : S} {x : s} (h : Irreducible x) : (x : K) ≠ 0 := by
  obtain ⟨x, hx⟩ := x
  rintro rfl
  exact h.1 ((or_self _).mp (h.2 (a := ⟨0, hx⟩) (b := ⟨0, hx⟩) (by ext; simp)))

local notation "iKL" => algebraMap K L
local notation "vK" => valuation K
local notation "vL" => valuation L

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem valuation_map_irreducible_lt_one {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    vL (iKL ϖ) < 1 := by
  have : vK ↑ϖ < 1 := Valuation.integer.v_irreducible_lt_one hϖ
  rw [← (vK).map_one, ← Valuation.Compatible.srel_iff_lt] at this
  simpa using (Valuation.Compatible.srel_iff_lt (v := vL)).mp <|
    (ValuativeExtension.srel_iff_srel (B := L) (ϖ : K) 1).mpr this

instance _root_.Valuation.compatible_map {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation R Γ₀} [ValuativeRel R]
    {Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] (f : Γ₀ →*₀ Γ₁) (hf : StrictMono f)
    [v.Compatible] : (v.map f hf.monotone).Compatible :=
  ⟨fun _ _ ↦ (Valuation.Compatible.rel_iff_le (v := v) _ _).trans hf.le_iff_le.symm⟩

instance _root_.Valued.toNormedField.compatible (K : Type*) [Field K] [ValuativeRel K]
    [UniformSpace K] [IsUniformAddGroup K] [IsValuativeTopology K]
    [hv : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne] :
    letI := Valued.toNormedField K _;
    (NormedField.valuation (K := K)).Compatible :=
  (valuation K).compatible_map _ <| Valuation.RankOne.strictMono _

instance (ε) : (valuationOfIoo K ε).Compatible :=
  Valuation.compatible_map _ (rankOneOfIoo K ε).strictMono

attribute [local instance] inhabitedIoo

open NNReal

-- by Anand Rao and Mohit Hulse
instance : FiniteDimensional K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  letI := IsTopologicalAddGroup.toUniformSpace K
  letI := IsTopologicalAddGroup.toUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  -- choose an arbitrary rank one structure for `L` (i.e. an arbitrary `ℝ`-valued norm)
  letI : (Valued.v (R := L)).RankOne := rankOneOfIoo L default
  letI := Valued.toNontriviallyNormedField (L := L)
  have hϖ1 : ‖iKL ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr
    (valuation_map_irreducible_lt_one K L hϖ)
  -- pull back the norm on `L` to a norm on `K`
  letI : NormedField K :=
  { toUniformSpace := ‹UniformSpace K›
    __ := NormedField.induced K L (algebraMap K L) (algebraMap K L).injective,
    uniformity_dist := ?_ }
  letI : NontriviallyNormedField K := .ofNormNeOne ⟨ϖ, hϖ.ne_zero', hϖ1.ne⟩
  letI : NormedSpace K L :=
  { norm_smul_le a b := by rw [Algebra.smul_def a b, norm_mul]; rfl }
  exact FiniteDimensional.of_locallyCompactSpace (𝕜 := K) (E := L)
  -- Showing `uniformity_dist` for `K`
  let ε : Set.Ioo (0 : ℝ) 1 := ⟨‖ϖ‖, norm_pos_iff.mpr hϖ.ne_zero, hϖ1⟩
  -- install the rank one structure for `K` where `ϖK` goes to `‖iKL ϖK‖`.
  letI : (valuation K).RankOne := rankOneOfIoo K ε
  -- Showing that the two valuations on `K` are the same by comparing them on `ϖ`
  let v₁ : Valuation K ℝ≥0 := NormedField.valuation.comap iKL
  let v₂ : Valuation K ℝ≥0 := valuationOfIoo K ε
  have cv₁ : v₁.Compatible := ValuativeExtension.compatible_comap K _
  have cv₂ : v₂.Compatible := inferInstance
  have eq : v₁ = v₂ := valuation_ext K hϖ
    (by ext; simp [v₂, valuationOfIoo_irreducible hϖ]; rfl)
  -- Use a basis for the two filters required by `uniformity_dist` and show they are the same
  have b₁ := (IsValuativeTopology.hasBasis_nhds_zero' K).uniformity_of_nhds_zero
  have b₂ := Filter.hasBasis_biInf_principal' (ι := ℝ) (p := (· > 0))
    (s := ({p : K × K | dist p.1 p.2 < ·})) (fun ε₁ hε₁ ε₂ hε₂ ↦ ⟨min ε₁ ε₂, by aesop⟩) ⟨1, by simp⟩
  refine b₁.ext b₂ (fun i hi ↦ ?_) fun i hi ↦ ?_
  · have : 0 < Valuation.RankOne.hom (valuation K) i := by
      convert (Valuation.RankOne.strictMono (valuation K)) (zero_lt_iff.2 hi); simp
    obtain ⟨n, hn⟩ := _root_.exists_pow_lt_of_lt_one this hϖ1
    refine ⟨ε ^ n, pow_pos ε.2.1 n, fun p hp ↦ ?_⟩
    refine (Valuation.RankOne.strictMono (valuation K)).lt_iff_lt.mp ?_
    change dist _ _ < _ at hp; rw [dist_comm] at hp
    rw [← coe_lt_coe] at hn ⊢
    convert hp.trans hn
    change (v₂ (p.2 - p.1) : ℝ) = ‖iKL p.2 - iKL p.1‖
    rw [← map_sub]
    exact congr($eq.symm _)
  · obtain ⟨n, hn⟩ := _root_.exists_pow_lt_of_lt_one hi hϖ1
    refine ⟨(valuation K ϖ) ^ n, pow_ne_zero _ <| (map_ne_zero _).mpr hϖ.ne_zero', fun p hp ↦ ?_⟩
    replace hp := (Valuation.RankOne.strictMono (valuation K)).lt_iff_lt.mpr hp
    rw [← coe_lt_coe, map_pow, coe_pow] at hp
    change dist _ _ < i; rw [dist_comm]
    change _ < (v₂ _ ^ n : ℝ) at hp
    rw [← eq] at hp
    convert hp.trans hn
    change ‖iKL p.2 - iKL p.1‖ = _
    rw [← map_sub]
    exact congr($eq _)

instance isModuleTopology : IsModuleTopology K L :=
  let := IsTopologicalAddGroup.toUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let := rankOneOfIoo K default
  let := Valued.toNontriviallyNormedField (L := K)
  isModuleTopologyOfFiniteDimensional

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
lemma algebraMap_mem_integer (x : 𝒪[K]) : (algebraMap 𝒪[K] L) x ∈ 𝒪[L] := by
  rcases x with ⟨x, hx⟩
  change valuation L (algebraMap K L x) ≤ 1
  simpa only [map_one] using (ValuativeExtension.algebraMap_le (B := L)).mpr hx

-- by David Ang
instance : Algebra 𝒪[K] 𝒪[L] where
  smul r a := ⟨r • a, Algebra.smul_def r (a : L) ▸ mul_mem (algebraMap_mem_integer ..) a.2⟩
  algebraMap := (algebraMap K L).restrict 𝒪[K] 𝒪[L] fun x hx => algebraMap_mem_integer K L ⟨x, hx⟩
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem algebraMap_integers_apply_coe (x : 𝒪[K]) :
    (algebraMap 𝒪[K] 𝒪[L]) x = algebraMap K L x := rfl

-- done in `Continuity.lean` by Andrew and Maddy
instance : ContinuousSMul K L := inferInstance

instance : FaithfulSMul 𝒪[K] 𝒪[L] :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun _ _ h ↦ Subtype.ext <|
    FaithfulSMul.algebraMap_injective K L congr($h)

instance (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] :
  Module.Finite 𝒪[K] 𝒪[L] :=
  sorry

instance : IsScalarTower 𝒪[K] K L := inferInstance

instance : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl

/-- The `e[L/K]` of an extension of local fields (also called the ramification index) is such that
`vL(iKL ϖK) = vL(ϖL^e[L/K])`, or alternatively `𝓂[K] 𝒪[L] = 𝓂[L] ^ e`. -/
noncomputable def e : ℕ :=
  Ideal.ramificationIdx (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] 𝓂[L]

-- by Hanliu Jiang
theorem e_spec {ϖK : 𝒪[K]} {ϖL : 𝒪[L]} (hϖk : Irreducible ϖK) (hϖl : Irreducible ϖL) :
    Associated (ϖL ^ e K L) (algebraMap 𝒪[K] 𝒪[L] ϖK) := by
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (Ideal.span_singleton_eq_bot.not.mpr <| (map_ne_zero_iff (algebraMap 𝒪[K] 𝒪[L])
      (FaithfulSMul.algebraMap_injective _ _)).mpr hϖk.ne_zero) hϖl
  rw [← Ideal.span_singleton_eq_span_singleton, hr]
  congr 3
  rw [← Set.image_singleton, ← Ideal.map_span, ← Ideal.span_singleton_pow,
    ← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖk] at hr
  have := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖl
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [hr, this]
  rw [hr, ← this]
  exact (Ideal.pow_right_strictAnti _ IsDiscreteValuationRing.not_a_field'
    Ideal.IsPrime.ne_top').le_iff_ge.not.mpr (by omega)

theorem e_spec' :
    (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap _ _) =
    IsLocalRing.maximalIdeal 𝒪[L] ^ e K L := by
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hk := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖK
  have hl := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖL
  rw [hk, hl, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton]
  exact (e_spec K L hϖK hϖL).symm

/-- The `f[L/K]` of an extension of local fields, which is `[𝓀[L] : 𝓀[K]]`. It is also called the
inertia degree. -/
noncomputable def f : ℕ :=
  Ideal.inertiaDeg 𝓂[K] 𝓂[L]

instance : 𝓂[L].LiesOver 𝓂[K] := by
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hk := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖK
  refine ⟨le_antisymm ?_ fun _ ↦ mt <| IsUnit.map _⟩
  rw [← Ideal.map_le_iff_le_comap, hk, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, algebraMap_integers_apply_coe]
  exact valuation_map_irreducible_lt_one K L hϖK

instance : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers vK)]
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers vL)] at hx
  exact (ValuativeRel.isEquiv ((vL).comap iKL) vK).eq_one_iff_eq_one.mp hx

-- bad instance, it has the wrong smul
attribute [-instance] IsLocalRing.ResidueField.instAlgebra

attribute [-instance] IsLocalRing.ResidueField.field in
instance _root_.IsLocalRing.ResidueField.instAlgebra' {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] :
    Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  Ideal.Quotient.algebraQuotientOfLEComap <|
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 0 3).mp <| by infer_instance
  -- __ := Module.IsTorsionBySet.module fun x c ↦ by
  --   obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  --   refine (Submodule.Quotient.mk_eq_zero _).mpr (?_ : (c : R) • x ∈ _)
  --   rw [Algebra.smul_def]
  --   exact Ideal.mul_mem_right _ _ <| map_nonunit _ _ c.2
  -- algebraMap := IsLocalRing.ResidueField.map (algebraMap R S)
  -- commutes' _ _ := mul_comm _ _
  -- smul_def' c x := by
  --   obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  --   obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  --   exact congr(Ideal.Quotient.mk _ $(Algebra.smul_def c x))

@[simp] lemma _root_.IsLocalRing.ResidueField.algebraMap_residue {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] (x : R) :
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
      (IsLocalRing.residue R x) = IsLocalRing.residue S (algebraMap R S x) := rfl

instance _root_.IsLocalRing.ResidueField.instIsScalarTower' {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] :
    IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  .of_algebraMap_eq' rfl

noncomputable instance : Algebra 𝓀[K] 𝓀[L] := inferInstance
  -- Ideal.Quotient.algebraQuotientOfLEComap
  --   (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝓂[L])).ge

example : (inferInstanceAs (Algebra 𝓀[K] 𝓀[L])) = Ideal.Quotient.algebraQuotientOfLEComap
    (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝓂[L])).ge :=
  rfl

instance : FiniteDimensional 𝓀[K] 𝓀[L] := inferInstance

instance : Algebra.IsSeparable 𝓀[K] 𝓀[L] := Algebra.IsAlgebraic.isSeparable_of_perfectField

-- by Hanliu Jiang
theorem f_spec : Module.finrank 𝓀[K] 𝓀[L] = f K L := by
  simp only [f, Ideal.inertiaDeg, IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝓂[L]), ↓reduceDIte,
    IsLocalRing.ResidueField]

-- by Hanliu Jiang
theorem f_spec' : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[L] := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  letI : Fintype 𝓀[L] := Fintype.ofFinite _
  rw [← f_spec, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, Nat.card_eq_fintype_card]

-- by Hanliu Jiang
theorem e_pos : 0 < e K L := by
  refine pos_of_ne_zero fun h ↦ ?_
  have := (Ideal.LiesOver.over (P := 𝓂[L]) (p := 𝓂[K])).le
  rw [← Ideal.map_le_iff_le_comap, e_spec', h, pow_zero, Ideal.one_eq_top, top_le_iff] at this
  exact absurd this Ideal.IsPrime.ne_top'

theorem f_pos : 0 < f K L := Ideal.inertiaDeg_pos 𝓂[K] 𝓂[L]

section

theorem _root_.Ideal.IsMaximal.irreducible_of_ne_bot {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} [hI : I.IsMaximal] (ne_bot : I ≠ ⊥) : Irreducible I := by
  refine ⟨Ideal.isUnit_iff.not.mpr hI.ne_top, fun x y hxy ↦ ?_⟩
  rw [Ideal.isUnit_iff, Ideal.isUnit_iff]
  by_cases hx : x = ⊤
  · tauto
  by_cases hy : y = ⊤
  · tauto
  refine absurd hxy <| ne_of_gt ?_
  rw [← hI.eq_of_le hx (hxy ▸ Ideal.mul_le_right), ← hI.eq_of_le hy (hxy ▸ Ideal.mul_le_left)]
  simpa [sq] using Ideal.pow_right_strictAnti _ ne_bot hI.ne_top (by decide : 1 < 2)

@[simp] theorem _root_.IsDiscreteValuationRing.irreducible_maximalIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Irreducible (IsLocalRing.maximalIdeal R) :=
  Ideal.IsMaximal.irreducible_of_ne_bot IsDiscreteValuationRing.not_a_field'

theorem _root_.UniqueFactorizationMonoid.factors_irreducible_of_subsingleton_units
    {M : Type*} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    {x : M} (hx : Irreducible x) (hx₀ : x ≠ 0) :
    UniqueFactorizationMonoid.factors x = {x} := by
  obtain ⟨p, hp, hpx⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hx₀ hx dvd_rfl
  replace hpx := associated_iff_eq.mp hpx; subst hpx
  obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem hp
  have assoc := UniqueFactorizationMonoid.factors_prod hx₀
  rw [hm, Multiset.prod_cons, associated_iff_eq, mul_eq_left₀ hx₀] at assoc
  suffices m = 0 by rw [hm, this, Multiset.cons_zero]
  induction m using Multiset.induction with
  | empty => rfl
  | cons y m ih =>
    rw [Multiset.prod_cons] at assoc
    have := eq_one_of_mul_right assoc; subst this
    have : 1 ∈ UniqueFactorizationMonoid.factors x := by rw [hm]; aesop
    exact ((UniqueFactorizationMonoid.irreducible_of_factor 1 this).not_isUnit (by simp)).elim

theorem _root_.UniqueFactorizationMonoid.factors_spec_of_subsingleton_units
    {M : Type*} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    {x : M} {m : Multiset M} (h₀ : 0 ∉ m) (h₁ : Associated x m.prod) (h₂ : ∀ y ∈ m, Irreducible y) :
    UniqueFactorizationMonoid.factors x = m := by
  rw [associated_iff_eq] at h₁; subst h₁
  obtain _ | _ := subsingleton_or_nontrivial M
  · simp [Multiset.eq_zero_of_forall_notMem (s := m) (fun x ↦ by rwa [Subsingleton.elim x 0])]
  induction m using Multiset.induction with
  | empty => simp
  | cons x m ih =>
    have := UniqueFactorizationMonoid.factors_mul (by aesop : x ≠ 0)
      (Multiset.prod_ne_zero (mt Multiset.mem_cons_of_mem h₀))
    rw [associated_eq_eq, Multiset.rel_eq] at this
    rw [Multiset.prod_cons, this,
      UniqueFactorizationMonoid.factors_irreducible_of_subsingleton_units (by aesop) (by aesop),
      ih (by aesop) (by aesop), Multiset.singleton_add]

theorem _root_.IsDiscreteValuationRing.factors_maximalIdeal_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ} :
    UniqueFactorizationMonoid.factors (IsLocalRing.maximalIdeal R ^ n) =
    Multiset.replicate n (IsLocalRing.maximalIdeal R) :=
  UniqueFactorizationMonoid.factors_spec_of_subsingleton_units
    (Multiset.mem_replicate.not.mpr <| mt And.right IsDiscreteValuationRing.not_a_field'.symm)
    (by simp; rfl) (by simp [Multiset.mem_replicate])

theorem _root_.IsDiscreteValuationRing.factors_maximalIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    UniqueFactorizationMonoid.factors (IsLocalRing.maximalIdeal R) = {IsLocalRing.maximalIdeal R} :=
  by simpa using IsDiscreteValuationRing.factors_maximalIdeal_pow (n := 1)

end

lemma factors_map_maximalIdeal :
    UniqueFactorizationMonoid.factors (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K]) =
    Multiset.replicate (e K L) 𝓂[L] := by
  rw [e_spec', IsDiscreteValuationRing.factors_maximalIdeal_pow]

lemma toFinset_factors_map_maximalIdeal [DecidableEq (Ideal 𝒪[L])] :
    (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K])).toFinset =
    {𝓂[L]} := by
  rw [factors_map_maximalIdeal, Multiset.toFinset_replicate, if_neg (e_pos K L).ne']

-- by Chenyi Yang
theorem e_mul_f_eq_n : e K L * f K L = Module.finrank K L := by
  classical
  rw [← Ideal.sum_ramification_inertia 𝒪[L] 𝓂[K] _ _ IsDiscreteValuationRing.not_a_field',
    primesOverFinset, toFinset_factors_map_maximalIdeal, Finset.sum_singleton]; rfl

-- TODO: generalise to extensions of DVRs.
@[mk_iff] class IsUnramified : Prop where
  e_eq_one : e K L = 1

lemma _root_.Algebra.unramified_iff (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.Unramified R A ↔ Algebra.FormallyUnramified R A ∧ Algebra.FiniteType R A :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

-- by Chenyi Yang
theorem isUnramified_iff_map_maximalIdeal :
    IsUnramified K L ↔ Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] = 𝓂[L] := by
  rw [isUnramified_iff, e_spec']
  refine ⟨(· ▸ pow_one _), fun h ↦ ?_⟩
  exact (Ideal.pow_right_strictAnti (IsLocalRing.maximalIdeal 𝒪[L])
    IsDiscreteValuationRing.not_a_field' Ideal.IsPrime.ne_top').injective (by simpa)

lemma Ideal.map_injective {R S : Type*} [CommSemiring R] [CommSemiring S]
    {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E) :
    Function.Injective (Ideal.map e) := fun x y h ↦ by
  rw [← Ideal.comap_map_of_bijective e (EquivLike.bijective e) (I := x), h,
    Ideal.comap_map_of_bijective e (EquivLike.bijective e)]

theorem _root_.Algebra.IsSeparable.iff_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*}
    [Field A₁] [Ring B₁] [Field A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁ = (e₂ : B₁ →+* B₂).comp (algebraMap A₁ B₁)) :
    Algebra.IsSeparable A₁ B₁ ↔ Algebra.IsSeparable A₂ B₂ :=
  ⟨(·.of_equiv_equiv e₁ e₂ he), (·.of_equiv_equiv e₁.symm e₂.symm <| by
    rw [← (algebraMap A₂ B₂).comp_id, ← RingEquiv.comp_symm e₁, ← RingHom.comp_assoc,
      ← RingHom.comp_assoc, RingHom.comp_assoc _ (algebraMap A₂ B₂), he,
      ← RingHom.comp_assoc, e₂.symm_comp, RingHom.id_comp])⟩

/-- Extra flexibility in the choice of:
1. A localisation `R'` of `R` at `p`.
2. A localisation `S'` of `S` at `q`. -/
lemma Algebra.isUnramifiedAt_iff_map_eq' {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p]
    (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization.AtPrime R' p] [IsLocalRing R']
    (S' : Type*) [CommRing S'] [Algebra S S'] [IsLocalization.AtPrime S' q] [IsLocalRing S']
    [Algebra R S'] [IsScalarTower R S S']
    [Algebra R' S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R' S')] :
    Algebra.IsUnramifiedAt R q ↔
    Algebra.IsSeparable (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField S') ∧
    Ideal.map (algebraMap R S') p = IsLocalRing.maximalIdeal S' := by
  rw [Algebra.isUnramifiedAt_iff_map_eq R p]
  refine and_congr ?_ ?_
  · refine Algebra.IsSeparable.iff_of_equiv_equiv
      (IsLocalRing.ResidueField.mapEquiv <| Localization.algEquiv p.primeCompl R')
      (IsLocalRing.ResidueField.mapEquiv <| Localization.algEquiv q.primeCompl S') ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p)) <| Ideal.Quotient.ringHom_ext <|
      RingHom.ext fun x ↦ ?_
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, algebraMap_mk,
      IsLocalRing.ResidueField.mapEquiv_apply, AlgEquiv.toRingEquiv_toRingHom]
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_eq R (Localization.AtPrime p) p.ResidueField,
      RingHom.comp_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.algebraMap_residue,
      RingHom.coe_coe, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime q) q.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue,
      RingHom.coe_coe, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  · rw [← (Ideal.map_injective (Localization.algEquiv q.primeCompl S')).eq_iff,
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _ (p := IsLocalRing.maximalIdeal _)),
      ← Ideal.map_coe, Ideal.map_map, ← AlgEquiv.toAlgHom_toRingHom,
      IsScalarTower.algebraMap_eq R S, ← RingHom.comp_assoc, AlgHom.comp_algebraMap,
      ← IsScalarTower.algebraMap_eq]

instance _root_.isLocalization_self (R : Type*) [CommSemiring R] [IsLocalRing R] :
    IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) where
  map_units x := of_not_not x.2
  surj x := ⟨(x, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa⟩

instance : Algebra.IsSeparable 𝓀[K] 𝓀[L] :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

-- by Chenyi Yang
theorem isUnramified_iff_isUnramifiedAt : IsUnramified K L ↔ Algebra.IsUnramifiedAt 𝒪[K] 𝓂[L] := by
  haveI : Algebra.IsSeparable 𝓀[K] 𝓀[L] := inferInstance
  rw [isUnramified_iff_map_maximalIdeal, Algebra.isUnramifiedAt_iff_map_eq' 𝓂[K] 𝓂[L] 𝒪[K] 𝒪[L]]
  tauto

-- they forgot to make it polymorphic
lemma _root_.Algebra.unramifiedLocus_eq_univ_iff'
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.unramifiedLocus R A = Set.univ ↔ Algebra.FormallyUnramified R A := sorry

-- ditto
lemma _root_.Algebra.isOpen_unramifiedLocus' {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] : IsOpen (Algebra.unramifiedLocus R A) := sorry

-- by Chenyi Yang
theorem isUnramified_iff_unramified : IsUnramified K L ↔ Algebra.Unramified 𝒪[K] 𝒪[L] := by
  rw [Algebra.unramified_iff, isUnramified_iff_isUnramifiedAt,
    ← Algebra.unramifiedLocus_eq_univ_iff']
  let U : TopologicalSpace.Opens (PrimeSpectrum 𝒪[L]) :=
    ⟨Algebra.unramifiedLocus 𝒪[K] 𝒪[L], Algebra.isOpen_unramifiedLocus'⟩
  change _ ↔ (U : Set (PrimeSpectrum 𝒪[L])) = _ ∧ _
  rw [TopologicalSpace.Opens.coe_eq_univ, ← IsLocalRing.closedPoint_mem_iff]
  refine iff_self_and.mpr fun _ ↦ inferInstance

variable {K L} in
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
lemma _root_.ValuativeExtension.valuation_le_one_of_isIntegral
    {y : L} (hy : IsIntegral 𝒪[K] y) : valuation L y ≤ 1 := by
  refine le_of_not_gt fun h ↦ ?_
  obtain ⟨p, monic, hpy⟩ := hy
  rw [monic.as_sum, ← Polynomial.aeval_def, map_add, add_eq_zero_iff_eq_neg] at hpy
  refine absurd congr(valuation L $hpy) <| ne_of_gt ?_
  simp_rw [Valuation.map_neg, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, map_pow]
  refine (valuation L).map_sum_lt ?_ fun i hi ↦ ?_
  · exact pow_ne_zero _ <| ne_of_gt <| one_pos.trans h
  · rw [map_mul, map_pow]
    have := (ValuativeRel.isEquiv ((valuation L).comap (algebraMap K L))
      (valuation K)).le_one_iff_le_one.mpr (p.coeff i).2
    refine (mul_le_of_le_one_left' this).trans_lt ?_
    exact (pow_lt_pow_iff_right₀ h).mpr (Finset.mem_range.mp hi)

instance isIntegralClosure : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff {y} := by
    refine ⟨fun hy ↦ ⟨⟨_, ValuativeExtension.valuation_le_one_of_isIntegral hy⟩, rfl⟩, fun hy ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hy
    exact (Algebra.IsIntegral.isIntegral y).algebraMap

theorem isIntegral_iff {y : L} : IsIntegral 𝒪[K] y ↔ valuation L y ≤ 1 := by
  rw [IsIntegralClosure.isIntegral_iff (A := 𝒪[L]), ← Set.mem_range]
  erw [Subtype.range_val, Valuation.mem_integer_iff]

end extension_of_local_fields

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L]

/-
open scoped Valued in
#check (inferInstance : NormedField K)
#check (inferInstance : Valuation.RankOne (Valued.v (R := K)))
-/

attribute [local instance] inhabitedIoo

theorem isNonarchimedeanLocalField_of_valuativeExtension [FiniteDimensional K L]
    [ValuativeRel L] [ValuativeExtension K L] :
    ∃ (_ : TopologicalSpace L), IsNonarchimedeanLocalField L := by
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := rankOneOfIoo K default
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField (L := K)
  let := Valued.mk' (valuation L)
  have : IsValuativeTopology L := .of_zero fun _ ↦ Valued.mem_nhds_zero
  have : LocallyCompactSpace L := .of_finiteDimensional_of_complete K L
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have : IsNontrivial L := ⟨(valuation L).comap (algebraMap K L) ϖK,
    (map_ne_zero _).mpr hϖK.ne_zero', ne_of_lt <| valuation_map_irreducible_lt_one K L hϖK⟩
  exact ⟨inferInstance, ⟨⟩⟩

open scoped NormedField in
theorem isNonarchimedeanLocalField_of_finiteDimensional [FiniteDimensional K L] :
    ∃ (_ : ValuativeRel L) (_ : ValuativeExtension K L)
    (_ : TopologicalSpace L), IsNonarchimedeanLocalField L := by
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := rankOneOfIoo K default
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField (L := K)
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  haveI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm
    isNonarchimedean_spectralNorm
  let v := NormedField.valuation (K := L)
  haveI : ValuativeExtension K L := by
    refine ⟨fun x y ↦ ?_⟩
    rw [Valuation.Compatible.rel_iff_le (v := v),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K)]
    change spectralNorm K L _ ≤ spectralNorm K L _ ↔ _
    rw [spectralNorm_extends, spectralNorm_extends]
    change Valued.norm _ ≤ Valued.norm _ ↔ _
    rw [Valued.norm_def, Valued.norm_def, NNReal.coe_le_coe,
      (Valuation.RankOne.strictMono Valued.v).le_iff_le]
    rfl
  exact ⟨inferInstance, inferInstance, isNonarchimedeanLocalField_of_valuativeExtension K L⟩

include K in
theorem ext_extension (v₁ v₂ : ValuativeRel L) (t₁ t₂ : TopologicalSpace L)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _)
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁)
    (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂) : v₁ = v₂ ∧ t₁ = t₂ where
  left := ValuativeRel.ext_of_field fun y ↦ by
    -- they agree on being `≤ 1`, because they agree on integral elements, because
    -- being integral is an algebraic property.
    rw [@Valuation.Compatible.rel_iff_le _ _ _ _ (v := @valuation L _ v₁) v₁ _,
      @Valuation.Compatible.rel_iff_le _ _ _ _ (v := @valuation L _ v₂) v₂ _, map_one, map_one,
      ← @isIntegral_iff K _ _ _ _ L _ v₁ t₁, ← @isIntegral_iff K _ _ _ _ L _ v₂ t₂]
  right := -- they are both the module topology
    (@isModuleTopology K _ _ _ _ L _ v₁ t₁ _ _ e₁).eq_moduleTopology'.trans <|
    (@isModuleTopology K _ _ _ _ L _ v₂ t₂ _ _ e₂).eq_moduleTopology'.symm

theorem unique_isNonarchimedeanLocalField [FiniteDimensional K L] :
    ∃! i : ValuativeRel L × TopologicalSpace L,
      @ValuativeExtension K L _ _ _ i.1 _ ∧ @IsNonarchimedeanLocalField L _ i.1 i.2 :=
  let ⟨v, e, t, h⟩ := isNonarchimedeanLocalField_of_finiteDimensional K L
  ⟨(v, t), ⟨e, h⟩, fun _ lf ↦ Prod.ext_iff.mpr <| ext_extension K L _ _ _ _ lf.1 e lf.2 h⟩

end make_finite_extension

end IsNonarchimedeanLocalField
