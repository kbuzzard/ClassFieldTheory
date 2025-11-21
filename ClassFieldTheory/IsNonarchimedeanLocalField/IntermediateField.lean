/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import ClassFieldTheory.Mathlib.Topology.Algebra.Group.Basic

/-! # Intermediate field of local fields is local field -/

namespace IsNonarchimedeanLocalField

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

attribute [local instance] inhabitedIoo

instance (E : IntermediateField K L) : IsNonarchimedeanLocalField E := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := rankOneOfIoo K default
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField (L := K)
  let t₁ : TopologicalSpace E := inferInstance
  -- the topology structure on `E` given by the subspace topology (`t₁`) is a module topology
  have ht₁ : IsModuleTopology K E (τA := t₁) := isModuleTopologyOfFiniteDimensional
  -- previous theorem: valuative extension -> topology (`t₂`) + local field
  let ⟨t₂, _⟩ := isNonarchimedeanLocalField_of_valuativeExtension K E
  -- the given `t₂` is also a module topology because it makes `E` a local field
  have ht₂ : IsModuleTopology K E (τA := t₂) := inferInstance
  -- therefore they are the same topology
  have := ht₂.1.trans ht₁.1.symm; subst this
  infer_instance

end IsNonarchimedeanLocalField
