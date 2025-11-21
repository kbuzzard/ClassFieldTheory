import Mathlib.Topology.Algebra.Monoid

instance (M σ : Type*) [Add M] [TopologicalSpace M] [ContinuousAdd M]
    [SetLike σ M] [AddMemClass σ M] (s : σ) : ContinuousAdd s :=
  ContinuousAdd.induced <| AddMemClass.subtype s

instance (M σ : Type*) [Mul M] [TopologicalSpace M] [ContinuousMul M]
    [SetLike σ M] [MulMemClass σ M] (s : σ) : ContinuousMul s :=
  ContinuousMul.induced <| MulMemClass.subtype s
