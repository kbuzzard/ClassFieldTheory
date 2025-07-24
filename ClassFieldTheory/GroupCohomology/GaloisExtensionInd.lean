import ClassFieldTheory.GroupCohomology._7_coind1_and_ind1
import ClassFieldTheory.GroupCohomology.NormalBasisTheorem

namespace AlgEquiv
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp] lemma apply_inv_self (e : A ≃ₐ[R] A) (x : A) : e (e⁻¹ x) = x := e.toEquiv.apply_symm_apply _
@[simp] lemma inv_apply_self (e : A ≃ₐ[R] A) (x : A) : e⁻¹ (e x) = x := e.toEquiv.symm_apply_apply _

end AlgEquiv

universe u

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

open scoped CategoryTheory
open scoped TensorProduct

noncomputable def galois_extension_iso_ind₁ :
    (Rep.ind₁ (L ≃ₐ[K] L)).obj (.of K K) ≅ Rep.of (AlgEquiv.toLinearMapHom K L) := by
  refine (Rep.ind₁AsFinsuppIso (G := (L ≃ₐ[K] L)) (.of K K)).symm ≪≫
    Action.mkIso (LinearEquiv.toModuleIso
      ((IsGalois.normalBasis K L).reindex (Equiv.inv (L ≃ₐ[K] L))).repr.symm) ?_
  intro x
  ext f
  simp only [Rep.ind₁AsFinsupp_V, Rep.trivialFunctor_obj_V, LinearEquiv.toModuleIso_hom,
    Basis.coe_repr_symm, Basis.coe_reindex, Equiv.inv_symm, Equiv.inv_apply, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    AlgEquiv.toLinearMapHom_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, 
    Finsupp.sum_fintype _ _ (fun i => by exact zero_smul K _),
    Finsupp.sum_fintype _ _ (fun i => by exact zero_smul K _)]
  unfold Rep.ind₁AsFinsupp
  simp only [Rep.ind₁'_obj, Rep.trivialFunctor_obj_V, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    Function.comp_apply, Representation.ind₁'_apply, map_sum, map_smul]
  unfold ModuleCat.endRingEquiv
  simp only [RingEquiv.symm_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, ModuleCat.ofHom_comp,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.lmapDomain_apply]
  apply Fintype.sum_equiv (Equiv.mulRight x)
  intro y
  rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => rfl), Finsupp.mapRange_apply]
  simp only [Equiv.coe_mulRight, mul_inv_rev]
  rw [IsGalois.normalBasis_apply y⁻¹, IsGalois.normalBasis_apply (x⁻¹ * y⁻¹)]
  simp only [AlgEquiv.mul_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_inv_self]
  congr 1
  change Finsupp.mapDomain (Equiv.mulRight x).symm _ _ = _
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]
  simp only [Equiv.mulRight_symm, inv_inv, Equiv.coe_mulRight]
