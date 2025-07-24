import Mathlib.Algebra.Homology.ShortComplex.Basic

namespace CategoryTheory

lemma ShortComplex.map_id {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] (S : ShortComplex C) :
  S.map (𝟭 C) = S := rfl

lemma ShortComplex.map_comp {C D E : Type*} [Category C] [Category D]
    [Category E] [Limits.HasZeroMorphisms C] (S : ShortComplex C)
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (F : Functor C D) [F.PreservesZeroMorphisms] (G : Functor D E) [G.PreservesZeroMorphisms] :
  S.map (F ⋙ G) = (S.map F).map G := rfl
