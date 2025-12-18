import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace IsLocalRing.ResidueField

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

-- bad instance, it has the wrong smul
attribute [-instance] instAlgebra

attribute [-instance] field in
instance instAlgebra' : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  Ideal.Quotient.algebraQuotientOfLEComap <|
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 0 3).mp <| by infer_instance

end IsLocalRing.ResidueField
