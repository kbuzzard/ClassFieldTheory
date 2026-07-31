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
def subtype (w : Subrepresentation ρ) :
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

variable {ρ}
/-- `w` interpreted as a `G`-rep. -/
abbrev toRep (w : Subrepresentation ρ) : Rep k G := .of w.toRepresentation

abbrev toRepSubtype (w : Subrepresentation ρ) : w.toRep ⟶ Rep.of ρ :=
  Rep.ofHom w.subtype

abbrev toRepTopIso (A : Rep.{w} k G) :
    (⊤ : Subrepresentation A.ρ).toRep ≅ A :=
  Rep.mkIso <| Subrepresentation.topEquiv A.ρ

/-- `A ⟶ A ⧸ w`. -/
abbrev quotient (w : Subrepresentation ρ) :
    Representation k G (W ⧸ w.toSubmodule) :=
  .quotient ρ w.1 w.2

@[simps!, implicit_reducible]
def mkQ (w : Subrepresentation ρ) : ρ.IntertwiningMap w.quotient where
  __ := Submodule.mkQ _
  isIntertwining' g := by rfl

/-- `A ⧸ w` interpreted as a `G`-rep. -/
abbrev toRepQuot (w : Subrepresentation ρ) : Rep k G := .of w.quotient

/-- `A ⟶ A ⧸ w`. -/
abbrev toRepMkQ (w : Subrepresentation ρ) : Rep.of ρ ⟶ w.toRepQuot :=
  Rep.ofHom w.mkQ

@[simps!, implicit_reducible]
def equivOfEqTop {w : Subrepresentation ρ} (h : w = ⊤) : w.toRepresentation.Equiv ρ :=
  .mk (LinearEquiv.ofTop _ congr(toSubmodule $h)) fun _ ↦ rfl

abbrev toRepIsoOfEqTop {w : Subrepresentation ρ} (h : w = ⊤) : w.toRep ≅ .of ρ :=
  Rep.mkIso <| .mk (LinearEquiv.ofTop _ congr(toSubmodule $h)) fun _ ↦ rfl

@[simps, implicit_reducible]
def subrepresentationOf (w₁ w₂ : Subrepresentation ρ) :
    Subrepresentation w₂.toRepresentation where
  toSubmodule := w₁.1.submoduleOf w₂.1
  apply_mem_toSubmodule g _ h := w₁.2 g h

@[implicit_reducible]
def subrepresentationEquivOfLE {w₁ w₂ : Subrepresentation ρ} (h : w₁ ≤ w₂) :
    (w₁.subrepresentationOf w₂).toRepresentation.Equiv w₁.toRepresentation :=
  .mk (Submodule.submoduleOfEquivOfLe h) fun _ ↦ rfl

abbrev subrepOfIsoOfLE {w₁ w₂ : Subrepresentation ρ} (h : w₁ ≤ w₂) :
    (w₁.subrepresentationOf w₂).toRep ≅ w₁.toRep :=
  Rep.mkIso <| subrepresentationEquivOfLE h

@[simps!, implicit_reducible]
def inclusion {w₁ w₂ : Subrepresentation ρ} (h : w₁ ≤ w₂) :
    w₁.toRepresentation.IntertwiningMap w₂.toRepresentation where
  __ := Submodule.inclusion h
  isIntertwining' _ := rfl

abbrev toRepInclusion {w₁ w₂ : Subrepresentation ρ} (h : w₁ ≤ w₂) :
    w₁.toRep ⟶ w₂.toRep := Rep.ofHom (inclusion h)

lemma inclusion_comp_subtype {w₁ w₂ : Subrepresentation ρ} {h : w₁ ≤ w₂} :
    w₂.subtype.comp (w₁.inclusion h) = w₁.subtype :=
  rfl

open CategoryTheory in
@[reassoc (attr := simp), elementwise nosimp (attr := simp)]
lemma toRepInclusion_comp_subtype {w₁ w₂ : Subrepresentation ρ} {h : w₁ ≤ w₂} :
    (w₁.toRepInclusion h) ≫ w₂.toRepSubtype = w₁.toRepSubtype :=
  Rep.hom_ext inclusion_comp_subtype

/-- `w₁ ⧸ (w₁ ⊓ w₂)` -/
def subquotient (w₁ w₂ : Subrepresentation ρ) :
    Representation k G (w₁.toSubmodule ⧸ (w₂.subrepresentationOf w₁).1) :=
  (w₂.subrepresentationOf w₁).quotient

abbrev toRepSubquot (w₁ w₂ : Subrepresentation ρ) : Rep k G :=
  .of (w₁.subquotient w₂)

end Subrepresentation
