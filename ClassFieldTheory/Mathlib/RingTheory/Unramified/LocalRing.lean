import ClassFieldTheory.Mathlib.FieldTheory.Separable
import ClassFieldTheory.Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.LocalRing

/-- Extra flexibility in the choice of:
1. A localisation `R'` of `R` at `p`.
2. A localisation `S'` of `S` at `q`. -/
lemma Algebra.isUnramifiedAt_iff_map_eq' {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p]
    (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization.AtPrime R' p] [IsLocalRing R']
    (S' : Type*) [CommRing S'] [Algebra S S'] [IsLocalization.AtPrime S' q] [IsLocalRing S']
    [Algebra R S'] [IsScalarTower R S S']
    [Algebra R' S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R' S')] :
    Algebra.IsUnramifiedAt R q ↔
    Algebra.IsSeparable (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField S') ∧
    Ideal.map (algebraMap R S') p = IsLocalRing.maximalIdeal S' := by
  rw [Algebra.isUnramifiedAt_iff_map_eq R p]
  refine and_congr ?_ ?_
  · refine Algebra.IsSeparable.iff_of_equiv_equiv
      (IsLocalRing.ResidueField.mapEquiv <| Localization.algEquiv p.primeCompl R')
      (IsLocalRing.ResidueField.mapEquiv <| Localization.algEquiv q.primeCompl S') ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p)) <| Ideal.Quotient.ringHom_ext <|
      RingHom.ext fun x ↦ ?_
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, algebraMap_mk,
      IsLocalRing.ResidueField.mapEquiv_apply, AlgEquiv.toRingEquiv_toRingHom]
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_eq R (Localization.AtPrime p) p.ResidueField,
      RingHom.comp_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.algebraMap_residue,
      RingHom.coe_coe, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime q) q.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue,
      RingHom.coe_coe, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  · rw [← (Ideal.map_injective (Localization.algEquiv q.primeCompl S')).eq_iff,
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _ (p := IsLocalRing.maximalIdeal _)),
      ← Ideal.map_coe, Ideal.map_map, ← AlgEquiv.toAlgHom_toRingHom,
      IsScalarTower.algebraMap_eq R S, ← RingHom.comp_assoc, AlgHom.comp_algebraMap,
      ← IsScalarTower.algebraMap_eq]
