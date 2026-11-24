module

public import ClassFieldTheory

@[expose] public section

open IsNonarchimedeanLocalField CategoryTheory.Limits

open scoped ValuativeRel Pointwise

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

instance : TopologicalSpace (repUnitsInteger G K L) := inferInstanceAs(TopologicalSpace 𝒪[L]ˣ)

attribute [local implicit_reducible] Rep.ofMulDistribMulAction

structure IsSerreLattice (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) : Prop where
  subset_smul_integer : ∀ x ∈ B, ∃ y ∈ 𝒪[L], x = (ϖ : K) • y          -- B ⊆ ϖ𝒪[L]
  mul_mul_mem : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ 𝒪[L], x * y * z ∈ ϖ • B    -- B·B·𝒪[L] ⊆ ϖB
  exists_pow_smul_mem : ∃ m : ℕ, ∀ x ∈ 𝒪[L], (ϖ : K) ^ m • x ∈ B     -- ϖ^m 𝒪[L] ⊆ B
  smul_mem : ∀ g : G, ∀ x ∈ B, g • x ∈ B

noncomputable def subrepFamily (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B)
    (i : ℕ) : Subrepresentation (repUnitsInteger G K L).ρ where
  toSubmodule := AddSubgroup.toIntSubmodule <| Subgroup.toAddSubgroup (G := 𝒪[L]ˣ) {
    carrier := (fun u : 𝒪[L]ˣ ↦ u.1.1 - 1) ⁻¹' (ϖ ^ i • B)
    mul_mem' := by sorry
    one_mem' := by sorry
    inv_mem' := by sorry
  }
  apply_mem_toSubmodule := sorry

omit [Finite G] in
@[simp] lemma mem_subrepFamily (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B)
    (i : ℕ) (x : repUnitsInteger G K L) :
    x ∈ subrepFamily G ϖ B hB i ↔ ((Additive.toMul x : 𝒪[L]ˣ) : L) - 1 ∈ ϖ ^ i • B :=
  Iff.rfl

instance (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B) :
    IsFilterComplete (subrepFamily G ϖ B hB) where
  haus' {x} hi := by
    simp at hi
    sorry
  prec' := sorry

theorem subrepFamily_isOpen (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B) (i : ℕ) :
    IsOpen ((subrepFamily G ϖ B hB i).toSubmodule : Set ↑(repUnitsInteger G K L)) := sorry

/-- A `G`-stable `𝒪[K]`-submodule of `L`, as a subrepresentation of `L`. -/
noncomputable def subrepOfStable (B : Submodule 𝒪[K] L) (hB : ∀ g : G, ∀ x ∈ B, g • x ∈ B) :
    Subrepresentation (Representation.ofDistribMulAction ℤ G L) where
  toSubmodule := B.restrictScalars ℤ
  apply_mem_toSubmodule g x hx := by simpa using hB g x hx

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [Finite G] in
/-- If `B` is `G`-stable then so is `ϖ • B`. -/
lemma smul_stable (B : Submodule 𝒪[K] L) (hB : ∀ g : G, ∀ x ∈ B, g • x ∈ B) (ϖ : 𝒪[K]) :
    ∀ g : G, ∀ x ∈ ϖ • B, g • x ∈ ϖ • B := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [smul_comm]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (hB g y hy)

-- example (ϖ : 𝒪[K]) (i : ℕ) (l : L) : (ϖ) • l = (ϖ : K)• l := by exact
--   Subring.smul_def ϖ l

/-- The map `Vᵢ → B ⧸ ϖB`, `u ↦ [(u - 1) / ϖ ^ i]`. -/
noncomputable def subquotHom (ϖ : 𝒪[K]) (hϖ : ϖ ≠ 0) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B)
    (i : ℕ) : (subrepFamily G ϖ B hB i).toSubmodule →+
      (subrepOfStable G B hB.smul_mem).toSubmodule ⧸
        ((subrepOfStable G (ϖ • B) (smul_stable G B hB.smul_mem ϖ)).subrepresentationOf
          (subrepOfStable G B hB.smul_mem)).toSubmodule where
  toFun x := Submodule.Quotient.mk ⟨((ϖ : K) ^ i)⁻¹ • (((Additive.toMul x.1 : 𝒪[L]ˣ) : L) - 1), by
    obtain ⟨x, (hx : x ∈ subrepFamily G ϖ B hB i)⟩ := x
    simp only [mem_subrepFamily, subrepOfStable, Submodule.restrictScalars_mem] at hx ⊢
    obtain ⟨b, hb, hb'⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hx
    simpa [← hb', Algebra.smul_def, IsScalarTower.algebraMap_eq (𝒪[K]) K L, ← mul_assoc,
      -map_inv₀, -map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero i (mod_cast hϖ : ϖ.1 ≠ 0))]⟩
  map_zero' := by simp [Submodule.mem_submoduleOf]
  map_add' := by
    sorry

noncomputable def subrepFamilyQuotIso (ϖ : 𝒪[K]) (B : Submodule 𝒪[K] L) (hB : IsSerreLattice G ϖ B)
    (i : ℕ) : (subrepFamily G ϖ B hB i).toRepSubquot (subrepFamily G ϖ B hB (i + 1)) ≅
      (subrepOfStable G B hB.smul_mem).toRepSubquot
        (subrepOfStable G (ϖ • B) (smul_stable G B hB.smul_mem ϖ)) := Rep.mkIso <|
  .mk (AddEquiv.toIntLinearEquiv sorry) sorry

open scoped Pointwise in
variable (K L) in
lemma serre_cor81 : ∃ M : Subrepresentation (A := ℤ) (G := G) (repUnitsInteger G K L).ρ,
    IsOpen (M.toSubmodule : Set (repUnitsInteger G K L)) ∧ ∀ q : ℕ,
    Subsingleton (groupCohomology M.toRep (q + 1)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_integer K L hϖ (IsGaloisGroup.normalBasis G K L 1)
  let b := (IsGaloisGroup.normalBasis G K L).unitsSMul fun _ ↦
    Units.mk0 (ϖ ^ n) (pow_ne_zero _ (mod_cast hϖ.ne_zero))
  -- let A : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range b)
  obtain ⟨N, hN⟩ := exists_pow_smul_integer_mem_span K L b hϖ
  let B := ϖ ^ (N + 1) • Submodule.span 𝒪[K] (Set.range b)
  refine ⟨subrepFamily G ϖ B ?_ 0, subrepFamily_isOpen .., fun q ↦ ?_⟩
  · sorry
  · sorry
  -- have : Fintype (Set.range b) := @Fintype.ofFinite _ (Set.finite_range _).to_subtype
  -- have hA0 : ∀ y ∈ A, y ∈ 𝒪[L] := fun y hy ↦ by
  --   obtain ⟨f, rfl⟩ := Submodule.mem_span_iff_of_fintype.1 hy
  --   refine Subring.sum_mem _ (fun ⟨m, ⟨g, hg⟩⟩ _ ↦ ?_)
  --   simp only [← hg, Algebra.smul_def]
  --   refine mul_mem (algebraMap_mem_integer K L _) ?_
  --   rw [Module.Basis.unitsSMul_apply, IsGaloisGroup.normalBasis_apply, ← smul_comm]
  --   exact (invariant K).smul_mem g hn
  -- have hB : B.toAddSubgroup ≤ ϖ • (Subring.toAddSubgroup 𝒪[L]) := fun x hx ↦ by
  --   obtain ⟨y, hy1, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _|>.1 hx
  --   rw [pow_succ', mul_smul]
  --   refine AddSubgroup.smul_mem_pointwise_smul _ _ _ ?_
  --   simp only [Algebra.smul_def, map_pow, AddSubgroup.mem_mk, Subsemiring.coe_carrier_toSubmonoid,
  --     Subring.coe_toSubsemiring, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, SetLike.mem_coe]
  --   exact mul_mem (pow_mem (algebraMap_mem_integer K L ϖ) _) <| hA0 _ hy1
  -- let M₀ : Subgroup 𝒪[L]ˣ :=
  --   { carrier := (fun u : 𝒪[L]ˣ ↦ u.1.1 - 1) ⁻¹' B
  --     mul_mem' := fun {u v} hu hv ↦ by simp at hu hv ⊢ ; sorry
  --     one_mem' := by simp
  --     inv_mem' := fun {u} hu ↦ by simp; sorry }
  -- let M : Subrepresentation (A := ℤ) (G := G) (repUnitsInteger G K L).ρ :=
  -- { toSubmodule := AddSubgroup.toIntSubmodule <| Subgroup.toAddSubgroup (G := 𝒪[L]ˣ) M₀
  --   apply_mem_toSubmodule := sorry }
  -- use M, ?_, fun q ↦ ?_
  -- · have : IsOpen (B : Set L) := by
  --     simp only [Submodule.coe_pointwise_smul, B]
  --     refine IsOpen.smul₀ ?_ (pow_ne_zero _ <| mod_cast hϖ.ne_zero)
  --     rw [← Submodule.coe_toAddSubgroup]
  --     refine A.toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
  --     have := Filter.mem_of_superset
  --       ((Valuation.isOpen_integer.smul₀ (pow_ne_zero N (mod_cast hϖ.ne_zero))).mem_nhds
  --         (Set.zero_mem_smul_set (zero_mem 𝒪[L])))
  --       (Set.smul_set_subset_iff.2 hN)
  --     sorry
  --   exact this.preimage <| (continuous_subtype_val.comp Units.continuous_val).sub continuous_const
  -- · -- have := groupCohomology.subsingleton_of_subquotient (fun i ↦ ϖ ^ i • B)
  --   sorry
