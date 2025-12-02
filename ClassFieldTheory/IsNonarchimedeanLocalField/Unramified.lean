/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.IsNonarchimedeanLocalField.Adic
import ClassFieldTheory.IsNonarchimedeanLocalField.RamificationInertia
import ClassFieldTheory.LocalCFT.Teichmuller
import ClassFieldTheory.Mathlib.FieldTheory.Finite.IntermediateField
import ClassFieldTheory.Mathlib.RingTheory.HenselPolynomial
import ClassFieldTheory.Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Unramified extension of local field of a given degree

This file shows that if `K` is a non-archimedean local field and `n > 0` is any positive integer,
then there is a unique (up to in general non-unique isomorphism) unramified extension of `K` of
degree `n`.
-/

noncomputable section

namespace IsNonarchimedeanLocalField

open Polynomial ValuativeRel

/-- **The** unramified extension of degree `n > 0` of a given non-archimedean local field `K`. -/
def UnramifiedExtension (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Type _ :=
  SplittingField (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1 : K[X])
deriving Field, Algebra K, FiniteDimensional K

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (n : ℕ)

instance : ValuativeRel (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose

instance : ValuativeExtension K (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose

instance : TopologicalSpace (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose_spec.choose

instance : IsNonarchimedeanLocalField (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose_spec.choose_spec

instance UnramifiedExtension.isSplittingField :
    IsSplittingField K (UnramifiedExtension K n) (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1) :=
  .splittingField _

theorem UnramifiedExtension.splits :
    (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1 : (UnramifiedExtension K n)[X]).Splits := by
  simpa using (UnramifiedExtension.isSplittingField K n).splits

open UnramifiedExtension

section zero

theorem finrank_unramifiedExtension_zero : Module.finrank K (UnramifiedExtension K 0) = 1 := by
  have := UnramifiedExtension.isSplittingField K 0
  rw [pow_zero, Nat.sub_self, pow_zero, sub_self, isSplittingField_iff_intermediateField,
    rootSet_zero, IntermediateField.adjoin_empty,
    IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
  exact this.2

instance : Subsingleton (Subalgebra K (UnramifiedExtension K 0)) :=
  subsingleton_of_bot_eq_top <| Subalgebra.bot_eq_top_of_finrank_eq_one <|
    finrank_unramifiedExtension_zero K

instance : Subsingleton (IntermediateField K (UnramifiedExtension K 0)) :=
  IntermediateField.toSubalgebra_injective.subsingleton

end zero

section non_zero_lemmas

theorem card_pow_sub_one_ne_zero' (K : Type*) [Field K] [Finite K] {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card K ^ n - 1 :) : K) ≠ 0 := by
  have hp := Fact.mk <| CharP.prime_ringChar K
  have := ZMod.algebra
  rw [ne_eq, CharP.cast_eq_zero_iff, Module.natCard_eq_pow_finrank (K := ZMod (ringChar K)),
    Nat.card_zmod, ← pow_mul, Nat.dvd_sub_iff_right, Nat.dvd_one]
  · exact hp.out.ne_one
  · exact one_le_pow_of_one_le' hp.out.one_le _
  · exact dvd_pow_self _ <| mul_ne_zero Module.finrank_pos.ne' hn

theorem card_pow_sub_one_in_nat_ne_zero (K : Type*) [Field K] [Finite K] {n : ℕ} (hn : n ≠ 0) :
    Nat.card K ^ n - 1 ≠ 0 :=
  ne_zero_of_map (f := algebraMap ℕ K) <| card_pow_sub_one_ne_zero' K hn

theorem card_pow_sub_one_ne_zero (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L]
    {n : ℕ} (hn : n ≠ 0) : ((Nat.card K ^ n - 1 :) : L) ≠ 0 := by
  rw [← map_natCast (algebraMap K _), ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  have := Finite.of_injective _ (algebraMap K L).injective
  exact card_pow_sub_one_ne_zero' K hn

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

theorem card_residue_pow_sub_one_in_integers_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : 𝒪[L]) ≠ 0 := by
  refine ne_zero_of_map (f := algebraMap 𝒪[L] 𝓀[L]) ?_
  rw [map_natCast]
  exact card_pow_sub_one_ne_zero _ _ hn

theorem card_residue_pow_sub_one_in_field_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : L) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝒪[L] L), ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  exact card_residue_pow_sub_one_in_integers_ne_zero K L hn

end non_zero_lemmas

instance : IsGalois K (UnramifiedExtension K n) := by
  obtain _ | n := n
  · have := finrank_unramifiedExtension_zero K
    rw [← IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
    rw [← isGalois_iff_isGalois_top, ← this]
    exact isGalois_bot
  refine .of_separable_splitting_field (p := X ^ (Nat.card 𝓀[K] ^ (n + 1) - 1) - 1) ?_
  rw [X_pow_sub_one_separable_iff]
  exact card_residue_pow_sub_one_in_field_ne_zero K _ n.succ_ne_zero

variable {n} in
instance [NeZero n] :
    HasEnoughRootsOfUnity (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1) :=
  .of_splits (splits K n) <| card_residue_pow_sub_one_in_field_ne_zero K _ NeZero.out

example [NeZero n] : ∃ ζ : UnramifiedExtension K n, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem UnramifiedExtension.top_eq_adjoin_roots :
    (⊤ : Subalgebra K (UnramifiedExtension K n)) = Algebra.adjoin K
      (nthRootsFinset (Nat.card 𝓀[K] ^ n - 1) 1 : Finset (UnramifiedExtension K n)) := by
  rw [← (isSplittingField K n).adjoin_rootSet, rootSet, aroots, nthRootsFinset, nthRoots]
  simp

theorem UnramifiedExtension.top_eq_adjoin_primitive_root
    {ζ : UnramifiedExtension K n} (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    (⊤ : Subalgebra K (UnramifiedExtension K n)) = Algebra.adjoin K {ζ} := by
  obtain _ | n := n
  · subsingleton
  have := card_pow_sub_one_in_nat_ne_zero 𝓀[K] n.succ_ne_zero
  rw [top_eq_adjoin_roots]
  refine le_antisymm (Algebra.adjoin_le fun ω hω ↦ ?_) <|
    Algebra.adjoin_le <| Set.singleton_subset_iff.mpr <| Algebra.subset_adjoin ?_
  · rw [SetLike.mem_coe, mem_nthRootsFinset (pos_of_ne_zero this)] at hω
    obtain ⟨i, _, rfl⟩ := HasEnoughRootsOfUnity.exists_pow this hζ hω
    exact pow_mem (Algebra.subset_adjoin <| Set.mem_singleton _) _
  · rw [SetLike.mem_coe, mem_nthRootsFinset (pos_of_ne_zero this), hζ.1]

theorem UnramifiedExtension.intermediateFieldTop_eq_adjoin_primitive_root
    {ζ : UnramifiedExtension K n} (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    (⊤ : IntermediateField K (UnramifiedExtension K n)) = .adjoin K {ζ} :=
  IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ <| by
    simp [top_eq_adjoin_primitive_root _ _ hζ]

variable {n} in
private theorem finrank_unramifiedExtension_and_residue (hn : n ≠ 0) :
    Module.finrank K (UnramifiedExtension K n) = n ∧
    n ≤ Module.finrank 𝓀[K] 𝓀[UnramifiedExtension K n] := by
  have := NeZero.mk hn
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1)
  have : 1 < Nat.card 𝓀[K] ^ n := Nat.one_lt_pow hn Finite.one_lt_card
  have h₁ : IsIntegral 𝒪[K] ζ := .of_pow (n := Nat.card 𝓀[K] ^ n - 1) (by grind)
    (by rw [hζ.1]; exact isIntegral_one)
  lift ζ to 𝒪[UnramifiedExtension K n] using isIntegral_iff.mp h₁
  have h₂ : IsIntegral 𝒪[K] ζ := h₁.tower_bot Subtype.val_injective
  have h₃ : minpoly 𝒪[K] ζ.val = minpoly 𝒪[K] ζ :=
    minpoly.algHom_eq (Algebra.algHom _ _ _) Subtype.val_injective ζ
  have h₄ : minpoly 𝒪[K] ζ ∣ X ^ Nat.card 𝓀[K] ^ n - X := by
    rw [← map_dvd_map (f := algebraMap 𝒪[K] K) (FaithfulSMul.algebraMap_injective _ _)
      (minpoly.monic h₂), ← h₃, ← minpoly.isIntegrallyClosed_eq_field_fractions' K h₁]
    refine minpoly.dvd _ _ ?_
    rw [← Nat.sub_add_cancel (show 1 ≤ Nat.card 𝓀[K] ^ n by grind)]
    simp [pow_succ, hζ.1]
  let ⟨p, hp⟩ := CharP.exists 𝓀[K]
  have := Fact.mk <| CharP.char_is_prime 𝓀[K] p
  have := ZMod.algebra 𝓀[K] p
  have h₅ : p ∣ Nat.card 𝓀[K] ^ n := dvd_pow (Nat.card_zmod p ▸ AddSubgroup.card_dvd_of_injective
    (algebraMap (ZMod p) 𝓀[K]) (FaithfulSMul.algebraMap_injective _ _)) hn
  have h₆ : (map (IsLocalRing.residue 𝒪[K]) (minpoly 𝒪[K] ζ)).Separable :=
    Polynomial.Separable.of_dvd (by simpa using galois_poly_separable p _ h₅) <|
      map_dvd (IsLocalRing.residue _) h₄
  have key : map (IsLocalRing.residue 𝒪[K]) (minpoly 𝒪[K] ζ) =
      minpoly 𝓀[K] (IsLocalRing.residue _ ζ) :=
    minpoly.eq_of_irreducible_of_monic
      (irreducible_map_of_irreducible_of_separable_map (minpoly.monic h₂) (minpoly.irreducible h₂)
        h₆)
      (by rw [← IsLocalRing.ResidueField.algebraMap_eq 𝒪[K], aeval_map_algebraMap,
        show ⇑(IsLocalRing.residue 𝒪[UnramifiedExtension K n]) = Algebra.algHom 𝒪[K] _ _ from rfl,
        aeval_algHom_apply, minpoly.aeval, map_zero])
      ((minpoly.monic h₂).map _)
  have h₇ : IsIntegral 𝓀[K] (IsLocalRing.residue _ ζ) :=
    (h₂.map <| Algebra.algHom 𝒪[K] _ _).tower_top
  have hζ₁ := hζ.of_map_of_injective (Subring.subtype_injective _)
  have hζ₂ := hζ₁.map_of_ne_zero (IsLocalRing.residue _) <| card_pow_sub_one_ne_zero _ _ hn
  have h₈ : (minpoly 𝓀[K] ((IsLocalRing.residue 𝒪[UnramifiedExtension K n]) ζ)).natDegree = n :=
    FiniteField.degree_minpoly_of_isPrimitiveRoot hn hζ₂
  constructor
  · rw [← IntermediateField.finrank_top', intermediateFieldTop_eq_adjoin_primitive_root _ _ hζ,
      IntermediateField.adjoin.finrank (h₁.tower_top),
      minpoly.isIntegrallyClosed_eq_field_fractions' K h₁,
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _),
      ← Monic.natDegree_map (minpoly.monic h₁) (IsLocalRing.residue 𝒪[K]), h₃, key, h₈]
  · conv_lhs => rw [← h₈]
    exact minpoly.natDegree_le _

variable {n} in
@[simp] theorem finrank_unramifiedExtension (hn : n ≠ 0) :
    Module.finrank K (UnramifiedExtension K n) = n :=
  (finrank_unramifiedExtension_and_residue K hn).1

variable {n} in
@[simp] theorem f_unramifiedExtension (hn : n ≠ 0) :
    f K (UnramifiedExtension K n) = n := by
  refine le_antisymm ?_ (by simpa [hn, f] using (finrank_unramifiedExtension_and_residue K hn).2)
  conv_rhs => rw [← finrank_unramifiedExtension K hn]
  exact f_le_n _ _

instance : IsUnramified K (UnramifiedExtension K n) := .mk <| by
  obtain rfl | hn := eq_or_ne n 0
  · exact e_eq_one_of_n_eq_one _ _ <| finrank_unramifiedExtension_zero K
  rw [← Nat.mul_left_inj (ne_of_gt <| f_pos K (UnramifiedExtension K n)),
    one_mul, e_mul_f_eq_n]
  simp [hn]

instance : HasEnoughRootsOfUnity K (Nat.card 𝓀[K] - 1) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot 𝓀[K] (Nat.card 𝓀[K] - 1)
  have := Finite.one_lt_card (α := 𝓀[K])
  have : NeZero (Nat.card 𝓀[K] - 1) := .mk <| by grind
  exact ⟨⟨_, hζ.map_of_injective teichmuller_injective⟩, inferInstance⟩

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

/-- If `Kn` denotes the unramified extension of `K` of degree `n`, then `Kn` embeds into `L` if
`n ∣ f K L`. This is half of the universal property. -/
theorem nonempty_unramifiedExtension_alghom_of_dvd_f (n : ℕ) (hn : n ∣ f K L) :
    Nonempty (UnramifiedExtension K n →ₐ[K] L) := by
  have hf0 := NeZero.mk (f_pos K L).ne'
  have hn0 := NeZero.mk <| ne_zero_of_dvd_ne_zero hf0.out hn
  have h₁ := Nat.pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hn
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1)
  have h₂ := pos_of_ne_zero <| card_pow_sub_one_in_nat_ne_zero 𝓀[K] hn0.out
  have h₃ := pos_of_ne_zero <| card_pow_sub_one_in_nat_ne_zero 𝓀[K] hf0.out
  refine IntermediateField.nonempty_algHom_of_adjoin_splits
    (forall_eq.mpr ⟨.of_pow h₂ <| hζ.1 ▸ isIntegral_one,
      .splits_of_dvd (g := X ^ (Nat.card 𝓀[K] ^ n - 1) - C 1) ?_
        (X_pow_sub_C_ne_zero h₂ _) ?_⟩)
    (intermediateFieldTop_eq_adjoin_primitive_root K _ hζ).symm
  · rw [f_spec'] at h₁ h₃
    have := NeZero.mk h₃.ne'
    have := HasEnoughRootsOfUnity.of_dvd L h₁
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card 𝓀[K] ^ n - 1)
    simpa [Splits] using X_pow_sub_one_splits hζ'
  · conv_rhs => exact show _ = map (algebraMap K L) (X ^ (Nat.card 𝓀[K] ^ n - 1) - C 1) by simp
    rw [map_dvd_map', minpoly.dvd_iff]
    simp [hζ.1]

/-- Universal property (non-unique) of unramified extensions. -/
theorem nonempty_unramifiedExtension_alghom_iff_dvd_f {n : ℕ} (hn : n ≠ 0) :
    Nonempty (UnramifiedExtension K n →ₐ[K] L) ↔ n ∣ f K L :=
  ⟨fun ⟨φ⟩ ↦ f_unramifiedExtension K hn ▸ f_dvd_f φ,
  nonempty_unramifiedExtension_alghom_of_dvd_f _ _ _⟩

/-- If `L/K` is unramified, then `L` is isomorphic to `Kn` where `n = [L:K]`. -/
theorem nonempty_unramifiedExtension_algEquiv_of_isUnramified [IsUnramified K L] :
    Nonempty (UnramifiedExtension K (Module.finrank K L) ≃ₐ[K] L) := by
  obtain ⟨φ⟩ := nonempty_unramifiedExtension_alghom_of_dvd_f K L (Module.finrank K L)
    (IsUnramified.n_dvd_f K L)
  have : φ.fieldRange = ⊤ := IntermediateField.toSubalgebra_injective <|
    Subalgebra.toSubmodule_injective <| Submodule.eq_top_of_finrank_eq <| by
    change Module.finrank K (LinearMap.range φ.toLinearMap) = _
    rw [LinearMap.finrank_range_of_inj φ.toRingHom.injective,
      finrank_unramifiedExtension _ Module.finrank_pos.ne']
  exact ⟨(AlgEquiv.ofInjective φ φ.toRingHom.injective).trans <|
    (IntermediateField.equivOfEq this).trans <| IntermediateField.topEquiv⟩

/-- Any unramified extension is Galois. -/
instance [IsUnramified K L] : IsGalois K L :=
  let ⟨φ⟩ := nonempty_unramifiedExtension_algEquiv_of_isUnramified K L
  .of_algEquiv φ

/-- The maximal unramified subextension. -/
def maximalUnramified : IntermediateField K L :=
  (nonempty_unramifiedExtension_alghom_of_dvd_f K L (f K L) dvd_rfl).some.fieldRange

instance : IsUnramified K (maximalUnramified K L) := by
  unfold maximalUnramified
  infer_instance

variable {K L} (E : IntermediateField K L)

/-- The maximal unramified subextension is maximal. -/
theorem le_maximalUnramified_iff : E ≤ maximalUnramified K L ↔ IsUnramified K E := by
  refine ⟨fun h ↦ .comap <| show E →ₐ[K] maximalUnramified K L from Subalgebra.inclusion h,
    fun _ ↦ ?_⟩
  obtain ⟨φ₁⟩ := nonempty_unramifiedExtension_algEquiv_of_isUnramified K E
  have h₁ : Module.finrank K E ∣ f K L := .trans (IsUnramified.n_dvd_f K E) <| f_dvd_f_top ..
  obtain ⟨φ₂⟩ := nonempty_unramifiedExtension_alghom_of_dvd_f K (UnramifiedExtension K (f K L))
    (Module.finrank K E) (by simpa [f_unramifiedExtension _ (f_pos _ _).ne'])
  unfold maximalUnramified
  generalize Nonempty.some _ = φ₃
  rw [← IntermediateField.toSubalgebra_le_toSubalgebra, AlgHom.fieldRange_toSubalgebra,
    ← AlgHom.fieldRange_of_normal (E := E) (φ₃.comp (φ₂.comp φ₁.symm)),
    AlgHom.fieldRange_toSubalgebra]
  exact AlgHom.range_comp_le_range ..

end IsNonarchimedeanLocalField
