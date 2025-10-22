import Mathlib.Algebra.Homology.ShortComplex.Basic

namespace CategoryTheory.ShortComplex
open Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

@[simp] lemma map_id (S : ShortComplex C) : S.map (𝟭 C) = S := rfl

@[simp] lemma map_comp (S : ShortComplex C)
    (F : Functor C D) [F.PreservesZeroMorphisms] (G : Functor D E) [G.PreservesZeroMorphisms] :
  S.map (F ⋙ G) = (S.map F).map G := rfl

/-- The first map of a short complex, as a functor. -/
@[simps] def fFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.f
  map {S T} f := Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂

/-- The second map of a short complex, as a functor. -/
@[simps] def gFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.g
  map {S T} f := Arrow.homMk f.τ₂ f.τ₃ f.comm₂₃

end CategoryTheory.ShortComplex
