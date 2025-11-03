import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

lemma CategoryTheory.ShortComplex.cocyclesMk_surjective.{u, v, w} {C : Type u} [Category.{v, u} C] {FC : C → C → Type*}
    {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasForget₂ C Ab] [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
    (S : ShortComplex C) [S.HasHomology] (x : ↑((forget₂ C Ab).obj S.cycles)) :
    ∃ (x₂ : ↑((forget₂ C Ab).obj S.X₂)) (hx₂ : (ConcreteCategory.hom
    ((forget₂ C Ab).map S.g)) x₂ = 0), ShortComplex.cyclesMk _ x₂ hx₂ = x := by
  let y := (ShortComplex.abCyclesIso _).hom <| (S.mapCyclesIso (forget₂ C Ab)).inv x
  use y.1, y.2
  simp +zetaDelta [ShortComplex.cyclesMk]
