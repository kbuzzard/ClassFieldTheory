import Mathlib
import ClassFieldTheory.GroupCohomology._7_coind1_and_ind1
import ClassFieldTheory.GroupCohomology.NormalBasisTheorem


universe u

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

open scoped CategoryTheory
open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000


noncomputable def galois_extension_iso_ind₁ :
    (Rep.ind₁ (L ≃ₐ[K] L)).obj (.of K K) ≅ Rep.of (AlgEquiv.toLinearMapHom K L) := by
  refine Action.mkIso (LinearEquiv.toModuleIso ((Submodule.quotEquivOfEqBot _ ?_) ≪≫ₗ
    TensorProduct.rid K _ ≪≫ₗ
    ((IsGalois.normalBasis K L).reindex (Equiv.inv (L ≃ₐ[K] L))).repr.symm)) ?_
  · simp only [Rep.trivialFunctor_obj_V, Representation.Coinvariants.ker,
    Representation.tprod_apply, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
    Submodule.span_eq_bot, Set.mem_range, Prod.exists, Subtype.exists, Subgroup.mem_bot,
    exists_prop_eq, map_one, forall_exists_index, forall_apply_eq_imp_iff]
    sorry
  intro x
  ext f
  simp only [Rep.trivialFunctor_obj_V, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, Rep.ρ_hom, Rep.ind₁_obj_ρ, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.trans_apply, Basis.repr_symm_apply, Basis.coe_reindex,
    Equiv.inv_symm, Equiv.inv_apply, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe, AlgEquiv.toLinearMapHom_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  simp only [Function.comp_apply]
  rw [Finsupp.sum_fintype _ _ sorry, Finsupp.sum_fintype _ _ sorry]
  rw [map_sum]
  simp only [map_smul]
  sorry
    
