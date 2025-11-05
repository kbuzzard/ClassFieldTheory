/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RepresentationTheory.Rep

/-! # Subrepresentations -/

universe u

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
@[coe] noncomputable def toRep (w : Subrep A) : Rep k G :=
  .subrepresentation _ w.toSubmodule w.le_comap

/-- `w ⟶ A`. -/
@[simps!] noncomputable def subtype (w : Subrep A) : w.toRep ⟶ A :=
  A.subtype _ _

/-- `A ⧸ w` interpreted as a `G`-rep. -/
noncomputable def quotient (w : Subrep A) : Rep k G :=
  .quotient _ w.toSubmodule w.le_comap

/-- `A ⟶ A ⧸ w`. -/
@[simps!] noncomputable def mkQ (w : Subrep A) : A ⟶ w.quotient :=
  A.mkQ _ _

-- todo: complete lattice, two adjoint functors (aka galois insertions)
instance : SemilatticeInf (Subrep A) where
  inf w₁ w₂ := ⟨w₁.toSubmodule ⊓ w₂.toSubmodule, fun g ↦ inf_le_inf (w₁.le_comap g) (w₂.le_comap g)⟩
  inf_le_left w₁ _ := inf_le_left (a := w₁.toSubmodule)
  inf_le_right w₁ _ := inf_le_right (a := w₁.toSubmodule)
  le_inf w₁ _ _ := le_inf (a := w₁.toSubmodule)

instance : OrderTop (Subrep A) where
  top := ⟨⊤, fun _ _ _ ↦ trivial⟩
  le_top _ _ _ := trivial

noncomputable def subrepOf (w₁ w₂ : Subrep A) : Subrep w₂.toRep where
  toSubmodule := w₁.submoduleOf w₂.toSubmodule
  le_comap g := fun ⟨_, _⟩ h ↦ w₁.le_comap g h

noncomputable def subrepOfIsoOfLE {w₁ w₂ : Subrep A} (h : w₁ ≤ w₂) :
    (w₁.subrepOf w₂).toRep ≅ w₁.toRep :=
  Action.mkIso (Submodule.submoduleOfEquivOfLe h).toModuleIso

noncomputable def inclusion {w₁ w₂ : Subrep A} (h : w₁ ≤ w₂) : w₁.toRep ⟶ w₂.toRep where
  hom := ModuleCat.ofHom <| Submodule.inclusion h

/-- `w₁ ⧸ (w₁ ⊓ w₂)` -/
noncomputable def subquotient (w₁ w₂ : Subrep A) : Rep k G :=
  (w₂.subrepOf w₁).quotient

end Subrep
