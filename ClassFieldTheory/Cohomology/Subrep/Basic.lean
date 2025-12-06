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
variable {k G : Type u} [CommRing k] [Monoid G] {A : Rep k G}

lemma toSubmodule_injective : (toSubmodule : Subrep A → Submodule k A.V).Injective :=
  fun ⟨_, _⟩ _ _ ↦ by congr!

instance : SetLike (Subrep A) A.V where
  coe w := w.carrier
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

instance : AddSubgroupClass (Subrep A) A.V where
  add_mem {w} := w.add_mem
  zero_mem {w} := w.zero_mem
  neg_mem {w} := w.neg_mem

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

instance : Min (Subrep A) where
  min w₁ w₂ := ⟨w₁.toSubmodule ⊓ w₂.toSubmodule, fun g ↦ inf_le_inf (w₁.le_comap g) (w₂.le_comap g)⟩

@[simp] lemma toSubmodule_inf (w₁ w₂ : Subrep A) :
    (w₁ ⊓ w₂).toSubmodule = w₁.toSubmodule ⊓ w₂.toSubmodule := rfl

-- todo: complete lattice, two adjoint functors (aka galois insertions)
instance : SemilatticeInf (Subrep A) := toSubmodule_injective.semilatticeInf _ toSubmodule_inf

instance : OrderTop (Subrep A) where
  top := ⟨⊤, fun _ _ _ ↦ trivial⟩
  le_top _ _ _ := trivial

noncomputable def topIso : (⊤ : Subrep A).toRep ≅ A :=
  Action.mkIso Submodule.topEquiv.toModuleIso

noncomputable def isoOfEqTop {w : Subrep A} (h : w = ⊤) : w.toRep ≅ A :=
  Action.mkIso <| (LinearEquiv.ofTop _ congr(($h).toSubmodule)).toModuleIso

noncomputable def subrepOf (w₁ w₂ : Subrep A) : Subrep w₂.toRep where
  toSubmodule := w₁.submoduleOf w₂.toSubmodule
  le_comap g := fun ⟨_, _⟩ h ↦ w₁.le_comap g h

noncomputable def subrepOfIsoOfLE {w₁ w₂ : Subrep A} (h : w₁ ≤ w₂) :
    (w₁.subrepOf w₂).toRep ≅ w₁.toRep :=
  Action.mkIso (Submodule.submoduleOfEquivOfLe h).toModuleIso

noncomputable def inclusion {w₁ w₂ : Subrep A} (h : w₁ ≤ w₂) : w₁.toRep ⟶ w₂.toRep where
  hom := ModuleCat.ofHom <| Submodule.inclusion h

open CategoryTheory in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem inclusion_comp_subtype {w₁ w₂ : Subrep A} {h : w₁ ≤ w₂} :
    w₁.inclusion h ≫ w₂.subtype = w₁.subtype :=
  rfl

/-- `w₁ ⧸ (w₁ ⊓ w₂)` -/
noncomputable def subquotient (w₁ w₂ : Subrep A) : Rep k G :=
  (w₂.subrepOf w₁).quotient

end Subrep
