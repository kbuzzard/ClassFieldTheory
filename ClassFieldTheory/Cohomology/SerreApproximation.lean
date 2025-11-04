/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-! # An approximation lemma

Let `M` be a filtered `G`-module, i.e. given `G`-submodules `M_i ≤ M` indexed by `i : ℕ`, such that
`M = lim[<-] M/M_i`. Now fix `q : ℕ` and suppose that `∀ i : ℕ, H^(q+1)(G, M_i/M_{i+1}) = 0`. Then
`H^(q+1)(G, M) = 0`.

-/

universe u

-- to replace `IsAdicComplete`
/-- `M` is complete with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0` and any compatible
sequence `I → M` has a limit in `M`. -/
class IsFilterComplete (M : Type*) {ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  haus' : ∀ x : M, (∀ i, x ∈ F i) → x = 0
  prec' : ∀ x : (ι → M), (∀ i j, i ≤ j → x i - x j ∈ F i) → ∃ L : M, ∀ i, x i - L ∈ F i

/-- A subrepresentation is a submodule that is invariant under the `G`-action. -/
structure Subrep {k G : Type u} [CommRing k] [Monoid G] (A : Rep k G) extends Submodule k A.V where
  le_comap (g) : toSubmodule ≤ toSubmodule.comap (A.ρ g)

namespace Subrep
variable {k G : Type u} [CommRing k] [Monoid G] (A : Rep k G)

instance : SetLike (Subrep A) A.V where
  coe w := w.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by congr; exact SetLike.coe_injective h

instance : AddSubgroupClass (Subrep A) A.V where
  add_mem {w} := w.add_mem
  zero_mem {w} := w.zero_mem
  neg_mem {w} := w.neg_mem

variable {A}

/-- `w` interpreted as a `G`-rep. -/
noncomputable def toRep (w : Subrep A) : Rep k G :=
  .subrepresentation _ w.toSubmodule w.le_comap

/-- `A ⧸ w` interpreted as a `G`-rep. -/
noncomputable def quotient (w : Subrep A) : Rep k G :=
  .quotient _ w.toSubmodule w.le_comap

-- todo: complete lattice, two adjoint functors (aka galois insertions)
instance : SemilatticeInf (Subrep A) where
  inf w₁ w₂ := ⟨w₁.toSubmodule ⊓ w₂.toSubmodule, fun g ↦ inf_le_inf (w₁.le_comap g) (w₂.le_comap g)⟩
  inf_le_left w₁ _ := inf_le_left (a := w₁.toSubmodule)
  inf_le_right w₁ _ := inf_le_right (a := w₁.toSubmodule)
  le_inf w₁ _ _ := le_inf (a := w₁.toSubmodule)

noncomputable def subrepOf (w₁ w₂ : Subrep A) : Subrep w₂.toRep where
  toSubmodule := w₁.submoduleOf w₂.toSubmodule
  le_comap g := fun ⟨_, _⟩ h ↦ w₁.le_comap g h

/-- `w₁ ⧸ (w₁ ⊓ w₂)` -/
noncomputable def subquotient (w₁ w₂ : Subrep A) : Rep k G :=
  (w₂.subrepOf w₁).quotient

end Subrep

variable {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (M_ : ℕ → Subrep M)
  [IsFilterComplete M M_]

namespace groupCohomology

theorem subsingleton_of_subquotient (q : ℕ)
    (h : ∀ i, Subsingleton (groupCohomology ((M_ i).subquotient (M_ (i + 1))) (q + 1))) :
    Subsingleton (groupCohomology M (q + 1)) :=
  sorry

end groupCohomology
