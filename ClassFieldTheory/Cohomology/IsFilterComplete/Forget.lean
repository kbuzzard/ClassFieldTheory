/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Cohomology.IsFilterComplete.Basic

/-! # "Forgetful functors" preserve completeness

where we mean e.g. the functor that goes from Subrep to Submodule.

-/

-- Question: should we have the class `SetLike.HasForget`?

theorem IsFilterComplete.forget {M σ τ ι : Type*} [LE ι]
    [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M] [SetLike τ M] [AddSubgroupClass τ M]
    {forget : σ → τ} {F : ι → σ} (faithful : ∀ ⦃s⦄ x, x ∈ forget s ↔ x ∈ s)
    [IsFilterComplete F] : IsFilterComplete (forget ∘ F) where
  haus' x hx := Filtration.eq_zero F <| by simpa [faithful] using hx
  prec' x hx :=
    have this (s : σ) : AddSubgroup.ofClass (forget s) = .ofClass s :=
      AddSubgroup.ext (faithful ·)
    let f : FilterCauchySeq F := ⟨x, by simpa [this] using hx⟩
    ⟨limit F <| .mk _ f, fun i ↦ by simpa [faithful] using sub_limit_mem F f⟩
