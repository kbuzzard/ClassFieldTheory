/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Subrepresentation

/-! # Subrepresentations -/

@[expose] public section

universe w u v

variable {k G V W : Type*}

section semiring_monoid

variable [Semiring k] [Monoid G] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G W)

namespace Subrepresentation
instance : AddSubmonoidClass (Subrepresentation ρ) W where
  add_mem {w} := w.toSubmodule.add_mem
  zero_mem {w} := w.toSubmodule.zero_mem

/-- `w ⟶ A`. -/
@[simps!, implicit_reducible]
noncomputable def subtype (w : Subrepresentation ρ) :
    w.toRepresentation.IntertwiningMap ρ where
  __ := w.toSubmodule.subtype
  isIntertwining' g := by rfl

@[simps!, implicit_reducible]
def topEquiv :
    (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ where
  __ := Submodule.topEquiv
  isIntertwining' _ := rfl

instance : SupSet (Subrepresentation ρ) where
  sSup s := ⟨sSup (toSubmodule '' s), fun g ↦ by
    suffices sSup (toSubmodule '' s) ≤ (sSup (toSubmodule '' s)).comap (ρ g) from this
    apply sSup_le
    rintro _ ⟨w, hw, rfl⟩ x hx
    exact Submodule.mem_sSup.2 fun N h ↦ (h w.toSubmodule ⟨w, hw, rfl⟩) (w.2 g hx)⟩

instance : InfSet (Subrepresentation ρ) where
  sInf s := ⟨sInf (toSubmodule '' s), fun g ↦ by
    intro x hx
    rw [Submodule.mem_sInf] at hx ⊢
    rintro _ ⟨w, hw, rfl⟩
    exact w.2 g (hx _ ⟨w, hw, rfl⟩)⟩

@[simp]
lemma toSubmodule_le_iff {x y : Subrepresentation ρ} :
    x.toSubmodule ≤ y.toSubmodule ↔ x ≤ y :=
  Iff.rfl

variable {ρ} in
lemma toSubmodule_sSup (s : Set (Subrepresentation ρ)) :
    (sSup s).toSubmodule = ⨆ i ∈ s, i.toSubmodule :=
  show sSup (toSubmodule '' s) = ⨆ _, _ by
  rw [sSup_eq_iSup, iSup_image]

variable {ρ} in
lemma toSubmodule_sInf (s : Set (Subrepresentation ρ)) :
    (sInf s).toSubmodule = ⨅ i ∈ s, i.toSubmodule :=
  show sInf (toSubmodule '' s) = ⨅ _, _ by
  rw [sInf_eq_iInf, iInf_image]

instance : CompleteLattice (Subrepresentation ρ) :=
  toSubmodule_injective.completeLattice _ Iff.rfl Iff.rfl toSubmodule_sup toSubmodule_inf
    toSubmodule_sSup toSubmodule_sInf rfl rfl

end Subrepresentation

end semiring_monoid

namespace Subrepresentation

variable [Ring k] [Monoid G] [AddCommGroup W] [Module k W]
  (ρ : Representation k G W) [AddCommGroup V] [Module k V]
  (σ : Representation k G V)

instance : AddSubgroupClass (Subrepresentation ρ) W where
  add_mem {w} := w.toSubmodule.add_mem
  zero_mem {w} := w.toSubmodule.zero_mem
  neg_mem {w} := w.toSubmodule.neg_mem

/-- `w` interpreted as a `G`-rep. -/
noncomputable abbrev toRep (w : Subrepresentation ρ) : Rep k G := .of w.toRepresentation

noncomputable abbrev toRepTopIso (A : Rep.{w} k G) :
    (⊤ : Subrepresentation A.ρ).toRep ≅ A :=
  Rep.mkIso <| topEquiv A.ρ

-- /-- `A ⧸ w` interpreted as a `G`-rep. -/
-- noncomputable def quotient (w : Subrep A) : Rep k G :=
--   .quotient _ w.toSubmodule w.le_comap

-- /-- `A ⟶ A ⧸ w`. -/
-- @[simps!] noncomputable def mkQ (w : Subrep A) : A ⟶ w.quotient :=
--   A.mkQ _ _

#exit
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

end Subrepresentation
