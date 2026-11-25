module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# The ring of integers of a compatible valuation is open

* `Valuation.isOpen_range_algebraMap_integer`: for a valuation `v` compatible with the valuative
  relation on a commutative ring `R` with the valuative topology, the image of
  `algebraMap v.integer R` is open. This is `Valuation.isOpen_integer` in the form needed by
  lemmas such as `Submodule.IsLattice.isOpen`.
-/

public section

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]
  [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} [v.Compatible]

/-- For any valuation `v` compatible with the valuative relation on `R`, the image of
`algebraMap v.integer R` is open in the valuative topology. -/
theorem isOpen_range_algebraMap_integer : IsOpen (Set.range (algebraMap v.integer R)) := by
  simpa [Algebra.coe_algebraMap_ofSubsemiring] using isOpen_integer

end Valuation
