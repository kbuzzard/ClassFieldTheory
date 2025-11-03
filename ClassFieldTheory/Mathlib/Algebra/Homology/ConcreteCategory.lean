import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ConcreteCategory

open CategoryTheory in
lemma HomologicalComplex.cyclesMk_surjective {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasForget₂ C Ab] [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) {i : ι} (j : ι)
    (hj : c.next i = j) (x : ((forget₂ C Ab).obj (K.cycles i))) :
    ∃ (x₂ : ((forget₂ C Ab).obj (K.X i))) (hx₂ : (ConcreteCategory.hom
    ((forget₂ C Ab).map (K.d i j))) x₂ = 0), HomologicalComplex.cyclesMk K x₂ j hj hx₂ = x := by
  subst hj
  exact (K.sc i).cocyclesMk_surjective x
