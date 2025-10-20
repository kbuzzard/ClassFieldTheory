import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.Basic
import ClassFieldTheory.Mathlib.CategoryTheory.Abelian.Exact
import ClassFieldTheory.Mathlib.CategoryTheory.Limits.Shapes.Kernels

noncomputable section

namespace CategoryTheory.ShortComplex
open Abelian Limits

variable {C D : Type*} [Category C] [Category D]

section Abelian
variable [Abelian C]

/-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
to the coimage of the second map.

Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
@[simps!] def kernelIsoImage (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ gFunctor ⋙ kernelFunctor ≅ F ⋙ fFunctor ⋙ imageFunctor :=
  NatIso.ofComponents fun X ↦
    have := (hF X).mono_cokernelDesc
    kernel.congr _ _ (by simp) ≪≫
      kernelCompMono _ (cokernel.desc (F.obj X).f (F.obj X).g (F.obj X).zero)

/-- The cokernel of the first map of an exact complex in an abelian category is naturally isomorphic
to the coimage of the second map.

Note that we use the extra functor `F` to avoid talking about the category of exact complex. -/
@[simps!] def cokernelIsoCoimage (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ fFunctor ⋙ cokernelFunctor ≅ F ⋙ gFunctor ⋙ coimageFunctor :=
  NatIso.ofComponents fun X ↦
    have := (hF X).epi_kernelLift
    cokernel.congr _ _ (by simp) ≪≫
      cokernelEpiComp (kernel.lift (F.obj X).g (F.obj X).f (F.obj X).zero) _

end Abelian
end CategoryTheory.ShortComplex
