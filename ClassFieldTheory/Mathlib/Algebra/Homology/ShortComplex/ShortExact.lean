module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

public section

namespace CategoryTheory.ShortComplex
open Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

lemma shortExact_map_iff_of_natIso
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (S : ShortComplex C)
    (hIso : F ≅ G) : (S.map F).ShortExact ↔ (S.map G).ShortExact :=
  shortExact_iff_of_iso (S.mapNatIso hIso)

alias ⟨ShortExact.map_of_natIso, _⟩ := shortExact_map_iff_of_natIso

/-- A faithful functor which preserves the homology of `S` as well as monomorphisms and
epimorphisms detects short exactness of `S`. Compare `ShortComplex.exact_map_iff_of_faithful`. -/
lemma shortExact_map_iff_of_faithful (S : ShortComplex C) [S.HasHomology] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [F.Faithful] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms] :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨fun h ↦ .mk' (S.exact_map_iff_of_faithful F|>.1 h.1) (F.mono_of_mono_map h.2)
    (F.epi_of_epi_map h.3), fun h ↦ have := h.mono_f; have := h.epi_g; h.map F⟩

end CategoryTheory.ShortComplex
