module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
The contents of this file (the instance `Algebra (IsLocalRing.ResidueField R)
(IsLocalRing.ResidueField S)` for a local algebra map `R → S`, built with
`Ideal.Quotient.algebraQuotientOfLEComap` so that it has the quotient `smul`) have been upstreamed
to `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField.instAlgebra` is now
defined via `Ideal.Quotient.algebraOfLiesOver`, so it no longer needs to be removed downstream.
-/
