import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.CategoryTheory.Abelian.Basic

open CategoryTheory CategoryTheory.Limits

universe v u
variable {ι : Type*} {V : Type u} [Category.{v} V]

noncomputable section

namespace CategoryTheory.Abelian
variable [Abelian V] {A B C : V}

@[ext]
lemma coimage.ext (f : A ⟶ B) {g h : C ⟶ Abelian.coimage f}
    (w : g ≫ Abelian.factorThruCoimage f = h ≫ Abelian.factorThruCoimage f) : g = h :=
  (cancel_mono <| Abelian.factorThruCoimage f).1 w

/-- Any short complex with maps `f : A ⟶ B` and `g : B ⟶ C` gives rise to a map from the cokernel
of `f` to the kernel of `g`. -/
def cokernelToCoimage (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) : cokernel f ⟶ Abelian.coimage g :=
  cokernel.desc f (coimage.π g) <| by ext; simpa using w

end CategoryTheory.Abelian
