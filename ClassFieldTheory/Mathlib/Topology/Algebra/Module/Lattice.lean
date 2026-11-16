module

public import ClassFieldTheory.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Module.Lattice

/-!
# Lattices are open in the module topology

Let `S` be a commutative topological ring, let `M` be an `S`-module with the module topology, and
let `R` be a commutative ring such that `S` is an `R`-algebra and `Set.range (algebraMap R S)` is
open in `S`, i.e. the image of `R` is an open subring of `S` (for example, `R` the valuation ring
`𝒪[K]` of a nonarchimedean local field `S = K`, see `Valuation.isOpen_range_algebraMap_integer`).

* `Submodule.IsLattice.isOpen`: every `R`-lattice in `M` is open in `M`. This only uses that a
  lattice spans `M` over `S` (`Submodule.isOpen_of_span_eq_top`).
-/

public section

namespace Submodule.IsLattice

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [TopologicalSpace S]
  [IsTopologicalSemiring S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [TopologicalSpace M] [IsModuleTopology S M]

/-- Let `M` carry the module topology over a commutative topological ring `S`, and let `R → S`
have open image. Then every `R`-lattice in `M` is open in `M`. -/
theorem isOpen (hR : IsOpen (Set.range (algebraMap R S))) (N : Submodule R M) [IsLattice S N] :
    IsOpen (N : Set M) :=
  isOpen_of_span_eq_top hR IsLattice.span_eq_top

end Submodule.IsLattice
