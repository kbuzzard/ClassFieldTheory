module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open spans in modules with the module topology

Let `S` be a topological ring, let `M` be an `S`-module with the module topology, and let `R` be
a commutative semiring such that `S` is an `R`-algebra and `Set.range (algebraMap R S)` is open
in `S`, i.e. the image of `R` is an open subring of `S` (for example, `R` the valuation ring
`𝒪[K]` of a nonarchimedean local field `S = K`, see `Valuation.isOpen_range_algebraMap_integer`).

* `IsModuleTopology.isOpen_span_of_span_eq_top`: the `R`-span of a finite family spanning `M`
  over `S` is open in `M`. For example, the `R`-span of a finite `S`-basis `b` is open
  (use `b.span_eq`).
* `Submodule.isOpen_of_span_eq_top`: if `R` is a ring, then every `R`-submodule of `M` that
  spans `M` over `S` is open in `M`. No finiteness assumption on `M` is needed.
-/

public section

open Submodule

lemma fintype_linearCombination_map {ι R M : Type*} (S : Type*) [CommSemiring R] [Ring S]
    [Algebra R S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] [Fintype ι]
    {v : ι → M} : Fintype.linearCombination R v = Fintype.linearCombination S v ∘
      Pi.map fun _ ↦ algebraMap R S:= by
  ext
  simp [Fintype.linearCombination_apply]

lemma fintype_linearCombination_restrictScalars {ι R M : Type*} (S : Type*) [CommSemiring R] [Ring S]
    [Algebra R S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M] {v : ι → M} [Fintype ι] :
    Fintype.linearCombination R v = (Fintype.linearCombination S v).restrictScalars R ∘ₗ
      LinearMap.piMap fun _  ↦ Algebra.linearMap R S := by
  simp [← LinearMap.coe_injective.eq_iff, fintype_linearCombination_map S, Algebra.coe_linearMap]

namespace IsModuleTopology

variable {ι R S M : Type*} [CommSemiring R] [Ring S] [Algebra R S] [TopologicalSpace S]
  [IsTopologicalSemiring S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [TopologicalSpace M] [IsModuleTopology S M]

/-- Let `M` carry the module topology over a topological ring `S`, and let `R → S` have open
image. Then the `R`-span of a finite family spanning `M` over `S` is open in `M`. -/
theorem isOpen_span_of_span_eq_top [Finite ι] {v : ι → M} (hv : span S (Set.range v) = ⊤)
    (hR : IsOpen (Set.range (algebraMap R S))) : IsOpen (span R (Set.range v) : Set M) := by
  have := Fintype.ofFinite ι
  have hU : IsOpen (Set.univ.pi fun _ : ι ↦ Set.range (algebraMap R S)) :=
    isOpen_set_pi Set.finite_univ fun _ _ ↦ hR
  rw [← Fintype.range_linearCombination, LinearMap.coe_range,
    fintype_linearCombination_restrictScalars S, LinearMap.coe_comp, Set.range_comp,
    LinearMap.coe_piMap, Set.range_piMap, ← Set.range_domRestrict]
  refine IsOpenMap.isOpen_range (.domRestrict (isOpenMap_of_surjective ?_) ?_)
  · exact span_range_eq_top_iff_surjective_fintypeLinearCombination S v |>.1 hv
  · exact isOpen_set_pi (by simp) fun _ _ ↦ ‹_›

end IsModuleTopology

namespace Submodule

open Filter Topology

variable {R S M : Type*} [CommRing R] [Ring S] [Algebra R S] [TopologicalSpace S]
  [IsTopologicalSemiring S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- If `R → S` has open image, then an `R`-submodule `N` of `M` spanning `M` over `S` absorbs
every `m : M`: `a • m ∈ N` for all `a` close enough to `0`. -/
theorem eventually_smul_mem_of_span_eq_top (hR : IsOpen (Set.range (algebraMap R S)))
    {N : Submodule R M} (hN : span S (N : Set M) = ⊤) (m : M) :
    ∀ᶠ a in 𝓝 (0 : S), a • m ∈ N := by
  have hm : m ∈ span S (N : Set M) := by
    rw [hN]
    exact mem_top
  induction hm using span_induction with
  | mem x hx =>
    filter_upwards [hR.mem_nhds ⟨0, map_zero _⟩] with a ⟨r, hr⟩
    rw [← hr, algebraMap_smul]
    exact N.smul_mem r hx
  | zero => simp
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with a hx hy
    rw [smul_add]
    exact N.add_mem hx hy
  | smul c x _ hx =>
    filter_upwards [((continuous_mul_const c).tendsto' 0 0 (zero_mul c)).eventually hx] with a ha
    rwa [smul_smul]

variable [TopologicalSpace M] [IsModuleTopology S M]

/-- Let `M` carry the module topology over a topological ring `S`, and let `R → S` have open
image. Then every `R`-submodule of `M` that spans `M` over `S` is open. No finiteness assumption
on `M` is needed: the `R`-submodules absorbing every element of `M` form a basis at `0` of a
topology making `M` a topological `S`-module, which is coarser than the module topology. -/
theorem isOpen_of_span_eq_top (hR : IsOpen (Set.range (algebraMap R S))) {N : Submodule R M}
    (hN : span S (N : Set M) = ⊤) : IsOpen (N : Set M) := by
  have := IsTopologicalSemiring.toIsTopologicalRing (R := S) inferInstance
  let P : Submodule R M → Prop := fun N' ↦ ∀ m : M, ∀ᶠ a in 𝓝 (0 : S), a • m ∈ N'
  let B : ModuleFilterBasis S M :=
    { sets := {U | ∃ N' : Submodule R M, P N' ∧ (N' : Set M) = U}
      nonempty := ⟨_, ⊤, fun _ ↦ .of_forall fun _ ↦ mem_top, rfl⟩
      inter_sets := by
        rintro _ _ ⟨N₁, h₁, rfl⟩ ⟨N₂, h₂, rfl⟩
        refine ⟨_, ⟨N₁ ⊓ N₂, fun m ↦ ((h₁ m).and (h₂ m)).mono fun _ ↦ mem_inf.2, rfl⟩, ?_⟩
        rw [coe_inf]
      zero' := by
        rintro _ ⟨N', -, rfl⟩
        exact N'.zero_mem
      add' := by
        rintro _ ⟨N', hN', rfl⟩
        refine ⟨_, ⟨N', hN', rfl⟩, ?_⟩
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact N'.add_mem hx hy
      neg' := by
        rintro _ ⟨N', hN', rfl⟩
        refine ⟨_, ⟨N', hN', rfl⟩, fun x hx ↦ ?_⟩
        simpa using N'.neg_mem hx
      conj' := by
        rintro x₀ _ ⟨N', hN', rfl⟩
        refine ⟨_, ⟨N', hN', rfl⟩, fun x hx ↦ ?_⟩
        simpa using hx
      smul' := by
        rintro _ ⟨N', hN', rfl⟩
        refine ⟨_, hR.mem_nhds ⟨0, map_zero _⟩, _, ⟨N', hN', rfl⟩, ?_⟩
        rintro _ ⟨_, ⟨r, rfl⟩, x, hx, rfl⟩
        simpa using N'.smul_mem r hx
      smul_left' := by
        rintro x₀ _ ⟨N', hN', rfl⟩
        refine ⟨_, ⟨N'.comap (DistribSMul.toLinearMap R M x₀), fun m ↦ ?_, rfl⟩, ?_⟩
        · filter_upwards [((continuous_const_mul x₀).tendsto' 0 0 (mul_zero x₀)).eventually
            (hN' m)] with a ha
          simpa [mul_smul] using ha
        · intro x hx
          simpa using hx
      smul_right' := by
        rintro m₀ _ ⟨N', hN', rfl⟩
        exact hN' m₀ }
  have h1 : IsOpen[B.topology] (N : Set M) :=
    @AddSubgroup.isOpen_of_mem_nhds M _ B.topology _ N.toAddSubgroup 0 <|
      B.toAddGroupFilterBasis.mem_nhds_zero ⟨N, eventually_smul_mem_of_span_eq_top hR hN, rfl⟩
  rw [eq_moduleTopology S M]
  exact h1.mono (@moduleTopology_le S _ M _ _ B.topology B.continuousSMul _)

end Submodule
