import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ConcreteCategory

open CategoryTheory in
lemma HomologicalComplex.cyclesMk_surjective.{v, u, u_1, u_2} {C : Type u} [Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type v}
    [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasForget₂ C Ab] [Abelian C]
    [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology] {ι : Type u_2} {c : ComplexShape ι}
    (K : HomologicalComplex C c) {i : ι} (j : ι) (hj : c.next i = j)
    (x : ↑((forget₂ C Ab).obj (K.cycles i))) :
    ∃ (x₂ : ↑((forget₂ C Ab).obj (K.X i))) (hx₂ : (ConcreteCategory.hom
    ((forget₂ C Ab).map (K.d i j))) x₂ = 0), HomologicalComplex.cyclesMk K x₂ j hj hx₂ = x := by
  subst hj
  exact (K.sc i).cocyclesMk_surjective x
