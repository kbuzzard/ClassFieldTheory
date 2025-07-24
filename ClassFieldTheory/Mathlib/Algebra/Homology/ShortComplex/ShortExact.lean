import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace CategoryTheory.ShortComplex

lemma shortExact_map_iff_of_natIso {C D : Type*}
    [Category C] [Category D] [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    {F G : Functor C D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (S : ShortComplex C)
    (hIso : F ≅ G) : (S.map F).ShortExact ↔ (S.map G).ShortExact :=
  shortExact_iff_of_iso (S.mapNatIso hIso)

alias ⟨shortExact_map_of_natIso, _⟩ := shortExact_map_iff_of_natIso
