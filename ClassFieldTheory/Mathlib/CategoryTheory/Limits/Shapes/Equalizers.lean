import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

namespace CategoryTheory.Limits
variable {C : Type*} [Category C]

/-- The equalizer of a pair of morphisms is natural. -/
@[simps]
noncomputable def equalizerFunctor [HasEqualizers C] : (WalkingParallelPair ⥤ C) ⥤ C where
  obj fg := equalizer (fg.map .left) (fg.map .right)
  map {fg₁ fg₂} u := equalizer.lift (equalizer.ι _ _ ≫ u.app .zero)
    (by rw [Category.assoc, ← u.naturality, equalizer.condition_assoc]; simp)

/-- The coequalizer of a pair of morphisms is natural. -/
@[simps]
noncomputable def coequalizerFunctor [HasCoequalizers C] : (WalkingParallelPair ⥤ C) ⥤ C where
  obj fg := coequalizer (fg.map .left) (fg.map .right)
  map {fg₁ fg₂} u := coequalizer.desc (u.app .one ≫ coequalizer.π _ _)
    (by simp; rw [coequalizer.condition])

end CategoryTheory.Limits
