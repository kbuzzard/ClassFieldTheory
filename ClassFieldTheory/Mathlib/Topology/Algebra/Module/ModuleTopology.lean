module

public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Open spans in modules with the module topology

Let `S` be a topological ring, let `M` be an `S`-module with the module topology, and let `R` be
a commutative semiring such that `S` is an `R`-algebra and `Set.range (algebraMap R S)` is open
in `S` (for example, `R` the valuation ring `𝒪[K]` of a nonarchimedean local field `S = K`).

* `IsModuleTopology.isOpen_span_of_span_eq_top`: the `R`-span of a finite family spanning `M`
  over `S` is open in `M`. For example, the `R`-span of a finite `S`-basis `b` is open
  (use `b.span_eq`).
* `Submodule.isOpen_of_span_eq_top`: if `M` is a finite `S`-module, then every `R`-submodule
  of `M` that spans `M` over `S` is open in `M`.
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

variable {R S M : Type*} [CommSemiring R] [Ring S] [Algebra R S] [TopologicalSpace S]
  [IsTopologicalSemiring S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [TopologicalSpace M] [IsModuleTopology S M]

/-- Let `M` be a finite module over a topological ring `S`, with the module topology, and let
`R → S` have open image. Then every `R`-submodule of `M` that spans `M` over `S` is open. -/
theorem isOpen_of_span_eq_top [Module.Finite S M] (hR : IsOpen (Set.range (algebraMap R S)))
    {N : Submodule R M} (hN : span S (N : Set M) = ⊤) : IsOpen (N : Set M) := by
  have := IsModuleTopology.isTopologicalAddGroup S M
  -- `N` contains a finite set `t` spanning `M` over `S`; the `R`-span `U` of `t` is open, so
  -- `N = N ⊔ U = N + U` is open too.
  obtain ⟨t, htN, ht⟩ := fg_span_iff_fg_span_finset_subset _ |>.1 <| hN ▸ Module.Finite.fg_top
  have hU := IsModuleTopology.isOpen_span_of_span_eq_top (v := ((↑) : t → M)) (by simp_all) hR
  rw [Subtype.range_coe] at hU
  rw [← sup_eq_left.2 (span_le.2 htN), coe_sup]
  exact hU.add_left

end Submodule
