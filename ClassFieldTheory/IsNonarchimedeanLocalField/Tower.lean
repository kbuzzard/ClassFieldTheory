/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic

/-! # Local field extensions in a scalar tower

Let `F/L/K` be a scalar tower of **fields**, each of which is a **local field**.
If `L/K` and `F/K` are extensions of **local fields**, then so is `F/L`.

-/

namespace IsNonarchimedeanLocalField

variable (K L F : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

theorem of_tower_top [ValuativeExtension K L] [ValuativeExtension K F] :
    ValuativeExtension L F := by
  have : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite K L F
  let v₁ : ValuativeRel F := ‹_›
  let t₁ : TopologicalSpace F := ‹_›
  let l₁ : IsNonarchimedeanLocalField F := ‹_›
  -- previous theorem: `F/L` finite, so `F` has a valuative rel + topology that make local field
  obtain ⟨v₂, e₂, t₂, l₂⟩ := isNonarchimedeanLocalField_of_finiteDimensional L F
  -- but then we have two extensions `F/K`, which must be the same
  obtain ⟨rfl, rfl⟩ := ext_extension K F v₁ v₂ t₁ t₂ ‹_› (.trans (B := L)) l₁ l₂
  exact e₂

end IsNonarchimedeanLocalField
