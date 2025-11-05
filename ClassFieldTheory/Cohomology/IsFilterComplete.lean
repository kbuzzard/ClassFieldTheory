/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Subgroup.Defs

/-! # Completeness with respect to a filtration -/

-- to replace `IsHausdorff`
/-- `M` is Hausdorff with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0`. -/
class IsFilterHasudorff {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  haus' : ∀ x : M, (∀ i, x ∈ F i) → x = 0

-- to replace `IsPrecomplete`
/-- `M` is precomplete with respect to the filtration `M_i ≤ M` if any compatible
sequence `I → M` has a limit in `M`. -/
class IsFilterPrecomplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop where
  haus' : ∀ x : M, (∀ i, x ∈ F i) → x = 0
  prec' : ∀ x : (ι → M), (∀ i j, i ≤ j → x i - x j ∈ F i) → ∃ L : M, ∀ i, x i - L ∈ F i

-- to replace `IsAdicComplete`
/-- `M` is complete with respect to the filtration `M_i ≤ M` if `⋂ M_i = 0` and any compatible
sequence `I → M` has a limit in `M`. -/
class IsFilterComplete {M ι σ : Type*} [AddCommGroup M]
    [LE ι] [SetLike σ M] [AddSubgroupClass σ M] (F : ι → σ) : Prop
    extends IsFilterHasudorff F, IsFilterPrecomplete F
