import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace CategoryTheory.ShortComplex
open Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

lemma shortExact_map_iff_of_natIso
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (S : ShortComplex C)
    (hIso : F ≅ G) : (S.map F).ShortExact ↔ (S.map G).ShortExact :=
  shortExact_iff_of_iso (S.mapNatIso hIso)

alias ⟨ShortExact.map_of_natIso, _⟩ := shortExact_map_iff_of_natIso

end CategoryTheory.ShortComplex
