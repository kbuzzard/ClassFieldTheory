import ClassFieldTheory.Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic

instance (M σ : Type*) [Semiring M] [TopologicalSpace M] [IsTopologicalSemiring M]
    [SetLike σ M] [SubsemiringClass σ M] (s : σ) : IsTopologicalSemiring s := .mk

instance (M σ : Type*) [Ring M] [TopologicalSpace M] [IsTopologicalRing M]
    [SetLike σ M] [SubringClass σ M] (s : σ) : IsTopologicalRing s := .mk
