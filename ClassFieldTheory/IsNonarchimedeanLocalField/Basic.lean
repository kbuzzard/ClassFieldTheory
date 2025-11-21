import ClassFieldTheory.LocalCFT.Continuity
import ClassFieldTheory.Mathlib.Algebra.Order.GroupWithZero.Canonical
import ClassFieldTheory.Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
import ClassFieldTheory.Mathlib.Data.Int.WithZero
import ClassFieldTheory.Mathlib.RingTheory.DiscreteValuationRing.Basic
import ClassFieldTheory.Mathlib.RingTheory.Localization.AtPrime.Basic
import ClassFieldTheory.Mathlib.RingTheory.Unramified.Basic
import ClassFieldTheory.Mathlib.RingTheory.Unramified.LocalRing
import ClassFieldTheory.Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Non-Archimedean Local Fields

Basic properties of nonarch local fields.

## Main results

* `ℚₚ` is a nonarch local field (**TODO** currently sorried)
* `equivResidueField : 𝓀[K] ≃ₐ[𝒪[K]] 𝓂[K].ResidueField` for K nonarch local
* `valuationOfIoo (ε : Set.Ioo (0 : ℝ) 1) : Valuation K ℝ≥0` (sending a uniformiser to `ε`)
* `valuation_ext` : Two `Valuation`s which are compatible with the valuative structure
  are equal if they're equal on a uniformiser.
* We have the instance that a valuative extension of nonarch local fields is
  finite-dimensional.
* `IsNonarchimedeanLocalField.isModuleTopology` : the larger field in a valuative extension of
  nonarch local fields has the module topology for the smaller field.
* instance : extension of integer rings in a valuative extension of nonarch local fields
  is module-finite (**TODO** currently sorried)
* Basic API for `e` and `f` for a valuative extension of nonarch local fields up to and
  including `ef=[L:K]`.
* Definition of unramified extension (for nonarch local fields, so automatically finite).
* Integral closure of O_K in a valuative extension of nonarch local fields is O_L
* `isNonarchimedeanLocalField_of_valuativeExtension`:
  Finite-diml valuative extension of a nonarch local field is a nonarch local field
  (in the sense that an appropriate topology exists)
* `isNonarchimedeanLocalField_of_finiteDimensional`:
  Finite-diml extension of a nonarch local field is a nonarch local field
  (in the sense that an appropriate valuative structure and topology exist).
* `IsNonarchimedeanLocalField.ext_extension`: uniqueness of these structures.
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
  letI := IsTopologicalAddGroup.rightUniformSpace K
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
    exact NNReal.coe_lt_coe.mp <| one_lt_one_div ε.2.1 ε.2.2

variable {K}

theorem valueGroupWithZeroIsoInt_irreducible {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valueGroupWithZeroIsoInt K (valuation K ϖ) = .exp (-1) := by
  rw [exp_neg_one_def]
  simpa [(valueGroupWithZeroIsoInt K).surjective.forall] using
    ⟨Valuation.integer.v_irreducible_lt_one hϖ, fun _ ↦ le_valuation_irreducible_of_lt_one hϖ⟩

theorem valuation_irreducible {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K ϖ = (valueGroupWithZeroIsoInt K).symm (.exp (-1)) := by
  rw [OrderMonoidIso.eq_symm_apply, valueGroupWithZeroIsoInt_irreducible hϖ]

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
  · exact NNReal.coe_lt_coe.mp <| one_lt_one_div ε.2.1 ε.2.2

noncomputable def inhabitedIoo : Inhabited (Set.Ioo (0 : ℝ) 1) := ⟨0.37, by norm_num, by norm_num⟩
attribute [local instance] inhabitedIoo

-- note: nonarch local fields have a *canonical* rank 1 valuation, sending
-- nonzero `x : K` to `addEquivAddHaarChar (t ↦ x * t)`. This example is not it.
noncomputable example : (valuation K).RankOne := rankOneOfIoo K default

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

-- keep
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
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  -- choose an arbitrary rank one structure for `L` (i.e. an arbitrary `ℝ`-valued norm)
  letI : (Valued.v (R := L)).RankOne := rankOneOfIoo L default
  letI := Valued.toNontriviallyNormedField (L := L)
  have hϖ1 : ‖iKL ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr
    (valuation_map_irreducible_lt_one hϖ)
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
  let := IsTopologicalAddGroup.rightUniformSpace K
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
@[simp] theorem algebraMap_integers_apply_coe (x : 𝒪[K]) :
    (algebraMap 𝒪[K] 𝒪[L]) x = algebraMap K L x := rfl

-- done in `Continuity.lean` by Andrew and Maddy
instance : ContinuousSMul K L := inferInstance

instance : FaithfulSMul 𝒪[K] 𝒪[L] :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun _ _ h ↦ Subtype.ext <|
    FaithfulSMul.algebraMap_injective K L congr($h)

-- some power series shenanigans
instance (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] :
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
  exact valuation_map_irreducible_lt_one hϖK

instance : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers vK)]
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers vL)] at hx
  exact (ValuativeRel.isEquiv ((vL).comap iKL) vK).eq_one_iff_eq_one.mp hx

-- bad instance, it has the wrong smul
attribute [-instance] IsLocalRing.ResidueField.instAlgebra

noncomputable instance : Algebra 𝓀[K] 𝓀[L] := inferInstance

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
  rw [← Ideal.sum_ramification_inertia (K := K) (L := L) (p := 𝓂[K]) 𝒪[L]
          IsDiscreteValuationRing.not_a_field',
      primesOverFinset, toFinset_factors_map_maximalIdeal, Finset.sum_singleton]
  rfl

theorem e_le_n : e K L ≤ Module.finrank K L :=
  e_mul_f_eq_n K L ▸ le_mul_of_one_le_right' <| f_pos K L

theorem f_le_n : f K L ≤ Module.finrank K L :=
  e_mul_f_eq_n K L ▸ le_mul_of_one_le_left' <| e_pos K L

-- TODO: standardize the spelling of "n = 1"
-- https://leanprover.zulipchat.com/#narrow/channel/516717-Oxford-Class-Field-Theory-2025-workshop/topic/trivial.20extension.20of.20local.20fields/with/557960349
theorem e_eq_one_of_n_eq_one (hn : Module.finrank K L = 1) : e K L = 1 :=
  le_antisymm (hn ▸ e_le_n K L) (e_pos K L)

-- TODO: standardize the spelling of "n = 1"
-- https://leanprover.zulipchat.com/#narrow/channel/516717-Oxford-Class-Field-Theory-2025-workshop/topic/trivial.20extension.20of.20local.20fields/with/557960349
theorem f_eq_one_of_n_eq_one (hn : Module.finrank K L = 1) : f K L = 1 :=
  le_antisymm (hn ▸ f_le_n K L) (f_pos K L)

-- TODO: generalise to extensions of DVRs.
@[mk_iff] class IsUnramified : Prop where
  e_eq_one' : e K L = 1

@[simp] theorem IsUnramified.e_eq_one [IsUnramified K L] : e K L = 1 := e_eq_one'

-- by Chenyi Yang
theorem isUnramified_iff_map_maximalIdeal :
    IsUnramified K L ↔ Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] = 𝓂[L] := by
  rw [isUnramified_iff, e_spec']
  refine ⟨(· ▸ pow_one _), fun h ↦ ?_⟩
  exact (Ideal.pow_right_strictAnti (IsLocalRing.maximalIdeal 𝒪[L])
    IsDiscreteValuationRing.not_a_field' Ideal.IsPrime.ne_top').injective (by simpa)

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

variable {K L} in
theorem isIntegral_iff {y : L} : IsIntegral 𝒪[K] y ↔ valuation L y ≤ 1 := by
  rw [IsIntegralClosure.isIntegral_iff (A := 𝒪[L]), ← Set.mem_range]
  erw [Subtype.range_val, Valuation.mem_integer_iff]

end extension_of_local_fields

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L]

attribute [local instance] inhabitedIoo

theorem isNonarchimedeanLocalField_of_valuativeExtension_of_isValuativeTopology
     [FiniteDimensional K L] [ValuativeRel L] [ValuativeExtension K L]
     [TopologicalSpace L] [IsValuativeTopology L] : IsNonarchimedeanLocalField L := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := rankOneOfIoo K default
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField (L := K)
  have : LocallyCompactSpace L := .of_finiteDimensional_of_complete K L
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have : IsNontrivial L := ⟨(valuation L).comap (algebraMap K L) ϖK,
    (map_ne_zero _).mpr hϖK.ne_zero', ne_of_lt <| valuation_map_irreducible_lt_one hϖK⟩
  exact ⟨⟩

theorem isNonarchimedeanLocalField_of_valuativeExtension [FiniteDimensional K L]
    [ValuativeRel L] [ValuativeExtension K L] :
    ∃ (_ : TopologicalSpace L), IsNonarchimedeanLocalField L := by
  let := Valued.mk' (valuation L)
  have : IsValuativeTopology L := .of_zero fun _ ↦ Valued.mem_nhds_zero
  exact ⟨inferInstance, isNonarchimedeanLocalField_of_valuativeExtension_of_isValuativeTopology K L⟩

open scoped NormedField in
theorem isNonarchimedeanLocalField_of_finiteDimensional [FiniteDimensional K L] :
    ∃ (_ : ValuativeRel L) (_ : ValuativeExtension K L)
    (_ : TopologicalSpace L), IsNonarchimedeanLocalField L := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
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
  exact ⟨ofValuation v, this, isNonarchimedeanLocalField_of_valuativeExtension K L⟩

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
