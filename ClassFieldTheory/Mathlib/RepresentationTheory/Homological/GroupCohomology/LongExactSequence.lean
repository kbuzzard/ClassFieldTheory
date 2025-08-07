import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

open CategoryTheory ShortComplex

universe u
variable {R G : Type u} [CommRing R] [Group G]

namespace groupCohomology

lemma map_cochainsFunctor_eval_shortExact (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact (X.map <| cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℕ) n) :=
  (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

end groupCohomology
