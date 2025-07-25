import Mathlib.Topology.Algebra.Module.FiniteDimension

/-- If `K` is a complete field and `L` is a finite dimensional vector space over `K`, and `K` is
locally compact, then `L` is locally compact.

This is not an instance because `K` cannot be inferred. -/
theorem locallyCompactSpace_of_complete_of_finiteDimensional (K L : Type*)
    [NontriviallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K]
    [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L] [T2Space L]
    [Module K L] [ContinuousSMul K L] [FiniteDimensional K L] :
    LocallyCompactSpace L := by
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis K L
  haveI := FiniteDimensional.fintypeBasisIndex b
  exact b.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace
