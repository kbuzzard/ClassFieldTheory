import ClassFieldTheory.Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [Abelian C]

/-- The image and coimage of an arrow are naturally isomorphic. -/
@[simps!]
def coimageFunctorIsoImageFunctor : coimageFunctor (C := C) ≅ imageFunctor :=
  NatIso.ofComponents fun _ ↦ Abelian.coimageIsoImage _

end CategoryTheory.Abelian
