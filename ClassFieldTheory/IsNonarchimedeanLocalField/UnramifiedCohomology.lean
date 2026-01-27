import ClassFieldTheory.IsNonarchimedeanLocalField.ValuationExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-! # Galois cohomology of unramified extensions of local fields

If `L/K` unramified then `H^q(Gal(L/K), 𝒪[L]ˣ) = 0` for `q > 0`.
-/

namespace IsNonarchimedeanLocalField
variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

open ValuativeRel
instance [IsUnramified K L] (q : ℕ) [NeZero q] :
    Subsingleton (groupCohomology (Rep.units Gal(L/K) 𝒪[L]) q) :=
  sorry

end IsNonarchimedeanLocalField
