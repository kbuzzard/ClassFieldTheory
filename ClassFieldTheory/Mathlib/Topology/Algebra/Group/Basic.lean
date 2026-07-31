module

public import ClassFieldTheory.Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Group.Basic

public section

instance (M σ : Type*) [Neg M] [TopologicalSpace M] [ContinuousNeg M]
    [SetLike σ M] [NegMemClass σ M] (s : σ) : ContinuousNeg s :=
  ⟨continuous_induced_rng.mpr <| by fun_prop⟩

instance (M σ : Type*) [AddGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [SetLike σ M] [AddSubgroupClass σ M] (s : σ) : IsTopologicalAddGroup s := .mk
