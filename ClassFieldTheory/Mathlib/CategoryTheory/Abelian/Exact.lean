import ClassFieldTheory.Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.CategoryTheory.Abelian.Exact

namespace CategoryTheory.ShortComplex
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {S : ShortComplex C}

open Abelian

lemma exact_iff_isIso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero) := by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply CategoryTheory.Limits.kernel.lift_mono

lemma Exact.isIso_imageToKernel (hS : S.Exact) : IsIso (imageToKernel S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel.1 hS

lemma Exact.isIso_imageToKernel' (hS : S.Exact) : IsIso (imageToKernel' S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel'.1 hS

proof_wanted exact_iff_isIso_cokernelToCoimage : S.Exact ↔ IsIso (cokernelToCoimage S.f S.g S.zero)

-- alias ⟨Exact.isIso_cokernelToCoimage, _⟩ := exact_iff_isIso_cokernelToCoimage

lemma Exact.mono_cokernelDesc (hS : S.Exact) : Mono (Limits.cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 hS

lemma Exact.epi_kernelLift (hS : S.Exact) : Epi (Limits.kernel.lift S.g S.f S.zero) :=
  S.exact_iff_epi_kernel_lift.1 hS

end CategoryTheory.ShortComplex
