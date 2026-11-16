module

public import ClassFieldTheory

@[expose] public section

open IsNonarchimedeanLocalField CategoryTheory.Limits

open scoped ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

instance : TopologicalSpace (repUnitsInteger G K L) := inferInstanceAs(TopologicalSpace 𝒪[L]ˣ)

open scoped Pointwise in
lemma serre_cor81 : ∃ M : Subrepresentation (A := ℤ) (G := G) (repUnitsInteger G K L).ρ,
    IsOpen (M.toSubmodule : Set (repUnitsInteger G K L)) ∧ ∀ q : ℕ,
    Subsingleton (groupCohomology M.toRep (q + 1)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_integer K L hϖ (IsGaloisGroup.normalBasis G K L 1)
  let b := (IsGaloisGroup.normalBasis G K L).unitsSMul fun _ ↦
    Units.mk0 (ϖ ^ n) (pow_ne_zero _ (mod_cast hϖ.ne_zero))
  let A : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range b)
  obtain ⟨N, hN⟩ := exists_pow_smul_integer_mem_span K L b hϖ
  let B := ϖ ^ (N + 1) • A
  have : Fintype (Set.range b) := @Fintype.ofFinite _ (Set.finite_range _).to_subtype
  have hA0 : ∀ y ∈ A, y ∈ 𝒪[L] := fun y hy ↦ by
    obtain ⟨f, rfl⟩ := Submodule.mem_span_iff_of_fintype.1 hy
    refine Subring.sum_mem _ (fun ⟨m, ⟨g, hg⟩⟩ _ ↦ ?_)
    simp only [← hg, Algebra.smul_def]
    refine mul_mem (algebraMap_mem_integer K L _) ?_
    rw [Module.Basis.unitsSMul_apply, IsGaloisGroup.normalBasis_apply, ← smul_comm]
    exact (invariant K).smul_mem g hn
  have hB : B.toAddSubgroup ≤ ϖ • (Subring.toAddSubgroup 𝒪[L]) := fun x hx ↦ by
    obtain ⟨y, hy1, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _|>.1 hx
    rw [pow_succ', mul_smul]
    refine AddSubgroup.smul_mem_pointwise_smul _ _ _ ?_
    simp only [Algebra.smul_def, map_pow, AddSubgroup.mem_mk, Subsemiring.coe_carrier_toSubmonoid,
      Subring.coe_toSubsemiring, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, SetLike.mem_coe]
    exact mul_mem (pow_mem (algebraMap_mem_integer K L ϖ) _) <| hA0 _ hy1
  let M₀ : Subgroup 𝒪[L]ˣ :=
    { carrier := (fun u : 𝒪[L]ˣ ↦ u.1.1 - 1) ⁻¹' B
      mul_mem' := fun {u v} hu hv ↦ by simp at hu hv ⊢ ; sorry
      one_mem' := by simp
      inv_mem' := fun {u} hu ↦ by simp; sorry }
  let M : Subrepresentation (A := ℤ) (G := G) (repUnitsInteger G K L).ρ :=
  { toSubmodule := AddSubgroup.toIntSubmodule <| Subgroup.toAddSubgroup (G := 𝒪[L]ˣ) M₀
    apply_mem_toSubmodule := sorry }
  use M, ?_, fun q ↦ ?_
  · have : IsOpen (B : Set L) := by
      simp only [Submodule.coe_pointwise_smul, B]
      refine IsOpen.smul₀ ?_ (pow_ne_zero _ <| mod_cast hϖ.ne_zero)
      rw [← Submodule.coe_toAddSubgroup]
      refine A.toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
      have := Filter.mem_of_superset
        ((Valuation.isOpen_integer.smul₀ (pow_ne_zero N (mod_cast hϖ.ne_zero))).mem_nhds
          (Set.zero_mem_smul_set (zero_mem 𝒪[L])))
        (Set.smul_set_subset_iff.2 hN)
      sorry
    exact this.preimage <| (continuous_subtype_val.comp Units.continuous_val).sub continuous_const
  · -- have := groupCohomology.subsingleton_of_subquotient (fun i ↦ ϖ ^ i • B)
    sorry
