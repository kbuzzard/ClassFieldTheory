import ClassFieldTheory.Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [Abelian C]

/-- The image and coimage of an arrow are naturally isomorphic -/
def coimageFunctorIsoImageFunctor : coimageFunctor (C := C) ≅ imageFunctor :=
  NatIso.ofComponents (fun M ↦ Abelian.coimageIsoImage _) fun {M N} f => by
    simp
    sorry

end CategoryTheory.Abelian
