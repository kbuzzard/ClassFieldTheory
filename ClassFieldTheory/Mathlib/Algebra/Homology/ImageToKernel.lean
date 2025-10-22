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

/-- Any short complex with maps `f : B ⟶ C` and `g : A ⟶ B` gives rise to a map from the cokernel
of `g` to the kernel of `f`. -/
def cokernelToCoimage (f : B ⟶ C) (g : A ⟶ B) (w : g ≫ f = 0) : cokernel g ⟶ Abelian.coimage f :=
  cokernel.desc g (coimage.π f) <| by ext; simpa using w

end CategoryTheory.Abelian
