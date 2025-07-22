import Mathlib

universe u v

namespace groupHomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker]
      /- have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this] -/
    mono_f := letI := hX.mono_f; chainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; chainsMap_id_f_map_epi X.g i }

end groupHomology
