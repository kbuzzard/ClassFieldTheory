import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

open CategoryTheory ShortComplex

universe u
variable {R G : Type u} [CommRing R] [Group G]

namespace groupHomology

lemma map_chainsFunctor_eval_shortExact (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact (X.map <| chainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (.down ℕ) n) :=
  (map_chainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

end groupHomology
