import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.LinearAlgebra.FreeProduct.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopkinsLevitzki

/- This file contains the normal basis theorem from Junyan's mathlib PR #27390 -/

namespace AlgEquiv

/- `AlgEquiv.toAlgHom` as a `MonoidHom`. -/
@[simps] def toAlgHomHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* A →ₐ[R] A where
  toFun := AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

end AlgEquiv

namespace AlgHom

section

universe u v w u₁ v₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- `AlgHom.toLinearMap` as a `MonoidHom`. -/
@[simps] def toEnd : (A →ₐ[R] A) →* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end

end AlgHom


section Semiring

variable {R M M' : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Module.annihilator_prod : annihilator R (M × M') = annihilator R M ⊓ annihilator R M' := by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]

theorem Module.annihilator_finsupp {ι : Type*} [Nonempty ι] :
    annihilator R (ι →₀ M) = annihilator R M := by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · let i := Classical.arbitrary ι
    classical simpa using fun m ↦ DFunLike.congr_fun (h (Finsupp.single i m)) i
  · intro m; ext i; exact h _

section

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem Module.annihilator_dfinsupp : annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _

theorem Module.annihilator_pi : annihilator R (Π i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

end

section frobenius

open FiniteField Finset

open Polynomial in
theorem minpoly_frobeniusAlgHom (K : Type u_1) [Field K] [Fintype K] (L : Type u_3) [Field L]
  [Algebra K L] [Finite L] :
    minpoly K (frobeniusAlgHom K L).toLinearMap = X ^ Module.finrank K L - 1 := by
  refine .symm <| minpoly.unique' _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x ↦ ?_) fun p lt ↦ or_iff_not_imp_left.mpr fun ne hp ↦ ne (ext fun i ↦ ?_)
  · simpa [sub_eq_zero, Module.End.coe_pow] using
      DFunLike.congr_fun (orderOf_dvd_iff_pow_eq_one.mp (orderOf_frobeniusAlgHom K L).dvd) x
  rw [← C_1, degree_X_pow_sub_C Module.finrank_pos] at lt
  rw [p.as_sum_range' _ ((natDegree_lt_iff_degree_lt ne).mpr lt)] at hp
  have := Fintype.linearIndependent_iff.mp ((linearIndependent_algHom_toLinearMap K L L).comp _
      (bijective_frobeniusAlgHom_pow K L).1) (algebraMap K L <| p.coeff ·) <| by
    simpa [sum_range, map_sum, aeval_monomial, ← AlgHom.toEnd_apply, ← map_pow] using hp
  obtain lt | le := lt_or_ge i (Module.finrank K L)
  · exact (algebraMap K L).injective (by simpa using this ⟨i, lt⟩)
  · exact coeff_eq_zero_of_degree_lt (lt.trans_le <| WithBot.coe_le_coe.mpr le)

end frobenius

section

open Module

open LinearMap in
theorem exists_ker_toSpanSingleton_eq_annihilator.{u, v} (R : Type u) [CommRing R]
  [IsPrincipalIdealRing R] (M : Type v) [AddCommGroup M] [Module R M] [IsDomain R]
  [Module.Finite R M] [Module.Finite R M] :
    ∃ x : M, ker (toSpanSingleton R _ x) = annihilator R M := by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ ↦ 1, DFinsupp.equivFunOnFintype.symm
    fun _ ↦ Submodule.mkQ _ 1), le_antisymm (fun x h ↦ ?_) fun x h ↦ mem_annihilator.mp h _⟩
  simp_rw [mem_ker, toSpanSingleton_apply, ← map_smul] at h
  rw [e.symm.map_eq_zero_iff, Prod.ext_iff, Finsupp.ext_iff, DFinsupp.ext_iff] at h
  obtain _ | m := m
  · simp_rw [e.annihilator_eq, annihilator_prod, annihilator_eq_top_iff.mpr inferInstance,
      DirectSum, annihilator_dfinsupp, top_inf_eq, Ideal.mem_iInf, mem_annihilator]
    intro i r
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ r
    rw [← mul_one r, ← smul_eq_mul, map_smul, ← mul_smul, mul_comm, mul_smul]
    exact congr(r • $(h.2 i)).trans (smul_zero _)
  · rw [show x = 0 by simpa using h.1 0]
    exact zero_mem _

end

namespace MvPolynomial

section

variable {R : Type*} [CommRing R] [IsDomain R]


private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (s : Fin n → Set R) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi .univ s, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    rw [RingEquiv.map_zero]
    convert h _ finZeroElim
  | succ n ih =>
    apply (finSuccEquiv R n).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((hs 0).image (C_injective ..).injOn).mono
    rintro _ ⟨r, hr, rfl⟩
    refine ih (s ·.succ) (fun _ ↦ hs _) fun x hx ↦ ?_
    rw [eval_polynomial_eval_finSuccEquiv]
    exact h _ fun i _ ↦ i.cases (by simpa using hr) (by simpa using hx)

variable {σ : Type*} {p q : MvPolynomial σ R} (s : σ → Set R) (hs : ∀ i, (s i).Infinite)
include hs

/-- Two multivariate polynomials over an integral domain are equal
if they are equal when evaluated anywhere in a box with infinite sides. -/
theorem funext_set (h : ∀ x ∈ Set.pi .univ s, eval x p = eval x q) :
    p = q := by
  suffices ∀ p, (∀ x ∈ Set.pi .univ s, eval x p = 0) → p = 0 by
    rw [← sub_eq_zero, this (p - q)]
    intro x hx
    simp_rw [map_sub, h x hx, sub_self]
  intro p h
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  suffices p = 0 by rw [this, map_zero]
  refine funext_fin (s ∘ f) (fun _ ↦ hs _) fun x hx ↦ ?_
  choose g hg using fun i ↦ (hs i).nonempty
  convert h (Function.extend f x g) fun i _ ↦ ?_
  · simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
  obtain ⟨i, rfl⟩ | nex := em (∃ x, f x = i)
  · rw [hf.extend_apply]; exact hx _ ⟨⟩
  · simp_rw [Function.extend, dif_neg nex, hg]

theorem funext_set_iff : p = q ↔ (∀ x ∈ Set.pi .univ s, eval x p = eval x q) :=
  ⟨by rintro rfl _ _; rfl, funext_set s hs⟩

end

end MvPolynomial

section

open Set Function Polynomial

theorem Module.AEval.X_pow_smul_of {R : Type u_2} {A : Type u_3} {M : Type u_1}
  [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M] (m : M) (n : ℕ) :
    (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m) := by
  rw [← of_aeval_smul, aeval_X_pow]

end

/-
# The normal basis theorem

We prove the normal basis theorem `IsGalois.exists_linearIndependent_algEquiv_apply`:
every finite Galois extension has a basis that is an orbit under the Galois group action.
-/

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

--attribute [reducible] AdjoinRoot in
open Polynomial FiniteField Module Submodule LinearMap in
private theorem exists_linearIndependent_algEquiv_apply_of_finite [Finite L] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  have := Finite.of_injective _ (algebraMap K L).injective
  have := Fintype.ofFinite K
  have ⟨x, hx⟩ := exists_ker_toSpanSingleton_eq_annihilator K[X]
    (AEval' (frobeniusAlgHom K L).toLinearMap)
  obtain ⟨x, rfl⟩ := (AEval'.of _).surjective x
  use x
  rw [← span_minpoly_eq_annihilator, minpoly_frobeniusAlgHom, eq_comm] at hx
  have ind := (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero Module.finrank_pos 1)).basis
    |>.linearIndependent.map' ((AEval'.of _).symm.toLinearMap ∘ₗ (Submodule.subtype _ ∘ₗ
      (quotEquivOfEq _ _ hx ≪≫ₗ quotKerEquivRange _).toLinearMap).restrictScalars K)
    (ker_eq_bot.mpr <| by simpa using EquivLike.injective _)
  rw [← linearIndependent_equiv ((finCongr <| natDegree_X_pow_sub_C (R := K)).trans <|
    .ofBijective _ <| bijective_frobeniusAlgEquivOfAlgebraic_pow K L)]
  convert ind
  ext i
  simp only [Function.comp_apply, AdjoinRoot.powerBasis, AdjoinRoot.powerBasisAux,
    coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, coe_subtype,
    Basis.coe_mk, LinearEquiv.trans_apply]
  erw [quotEquivOfEq_mk, quotKerEquivRange_apply_mk]
  simp [AEval.X_pow_smul_of, Module.End.coe_pow]
  rfl

variable [FiniteDimensional K L]

open scoped Classical in
private theorem exists_linearIndependent_algEquiv_apply_of_infinite [Infinite K] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  have e := Module.Free.chooseBasis K L
  let M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (MvPolynomial _ L) :=
    .of fun i j ↦ ∑ k, i.symm (j (e k)) • MvPolynomial.X k
  have hM : M.det ≠ 0 := by
    have hq : Submodule.span L (Set.range fun i (j : L ≃ₐ[K] L) ↦ j (e i)) = ⊤ := by
      rw [← Subspace.dualAnnihilator_inj, Submodule.dualAnnihilator_top, ← le_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := (Pi.basisFun L (L ≃ₐ[K] L)).toDualEquiv.surjective x
      rw [Submodule.mem_bot, ← LinearEquiv.eq_symm_apply, LinearEquiv.map_zero]
      rw [← SetLike.mem_coe, Submodule.coe_dualAnnihilator_span,
        Set.mem_setOf, Set.range_subset_iff] at hx
      simp_rw [SetLike.mem_coe, LinearMap.mem_ker, Basis.toDualEquiv_apply] at hx
      conv at hx =>
        enter [i, 1, 2, j]
        rw [← Fintype.sum_pi_single j fun j => j (e i), ← Finset.sum_apply]
        enter [2, c]
        rw [← mul_one (c (e i)), ← smul_eq_mul, Pi.single_smul', ← Pi.basisFun_apply]
      simp_rw [map_sum, map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul] at hx
      have ind := (linearIndependent_algHom_toLinearMap K L L).comp AlgEquiv.toAlgHom
        fun _ _ h => DFunLike.coe_injective (congrArg DFunLike.coe h :)
      rw [Fintype.linearIndependent_iff] at ind
      ext i
      rw [Pi.zero_apply]
      apply ind
      ext j
      rw [LinearMap.zero_apply, LinearMap.coeFn_sum, Finset.sum_apply]
      simp only [Function.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
        LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul]
      have h := Fintype.sum_eq_zero _
        fun i ↦ congr(e.repr j i • $(hx i)).trans (smul_zero (e.repr j i))
      conv at h =>
        enter [1, 2, i]
        rw [Finset.smul_sum]
        enter [2, k]
        rw [← smul_eq_mul, ← smul_assoc, ← map_smul]
      rw [Finset.sum_comm] at h
      conv at h =>
        enter [1, 2, k]
        rw [← Finset.sum_smul]
        enter [1]
        rw [← map_sum]
        enter [2]
        rw [e.sum_repr]
      simpa [mul_comm] using h
    obtain ⟨c, hc⟩ : ∃ c : _ → L, M.det.eval c = 1 := by
      have h := (congrArg (fun s ↦ Pi.single 1 1 ∈ s) hq).mpr (Submodule.mem_top ..)
      rw [← Set.image_univ, ← Finset.coe_univ,
        ← Function.Embedding.coeFn_mk (fun i (j : L ≃ₐ[K] L) ↦ j (e i))
          fun a b hab ↦ e.injective (congrFun hab .refl),
        ← Finset.coe_map, Submodule.mem_span_finset'] at h
      obtain ⟨f, hf⟩ := h
      let g k : L := f ⟨fun j ↦ j (e k), Finset.mem_map_of_mem _ (Finset.mem_univ k)⟩
      conv at hf =>
        enter [1, 2, a, 1]
        equals g (Function.invFun (fun i (j : L ≃ₐ[K] L) => j (e i)) a) =>
          apply congrArg f
          apply Subtype.ext
          symm
          apply Function.invFun_eq (f := fun i (j : L ≃ₐ[K] L) => j (e i))
          exact (Finset.mem_map.1 a.prop).imp fun _ => And.right
      rw [Finset.sum_coe_sort (Finset.map ..)
        fun a ↦ g (Function.invFun _ a) • a, Finset.sum_map] at hf
      conv at hf =>
        enter [1, 2, a, 1]
        equals g a =>
          apply congrArg f
          apply Subtype.ext
          apply Function.apply_invFun_apply (f := fun i (j : L ≃ₐ[K] L) => j (e i))
      simp_rw [Function.Embedding.coeFn_mk] at hf
      use g
      rw [RingHom.map_det]
      refine (congrArg Matrix.det ?_).trans Matrix.det_one
      ext i j
      simpa [M, Pi.single_apply, inv_mul_eq_one, mul_comm, Matrix.one_apply]
        using congrFun hf (i⁻¹ * j)
    have : Infinite L := .of_injective (algebraMap K L) (algebraMap K L).injective
    rw [ne_eq, MvPolynomial.funext_iff, not_forall]
    use c
    simp only [hc, map_zero, one_ne_zero, not_false_eq_true]
  obtain ⟨b, hb⟩ : ∃ b : _ → K, M.det.eval (algebraMap K L ∘ b) ≠ 0 := by
    by_contra! h
    apply hM
    apply MvPolynomial.funext_set fun _ => Set.range (algebraMap K L)
    · exact fun _ => Set.infinite_range_of_injective (algebraMap K L).injective
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_range, forall_const] at hx
      choose u hu using hx
      replace hu : algebraMap K L ∘ u = x := funext hu
      subst hu
      simpa using h u
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hb
  use ∑ k, b k • e k
  rw [linearIndependent_iff]
  intro a ha
  refine DFunLike.coe_injective (Function.Injective.comp_left ((algebraMap K L).injective) ?_)
  dsimp
  simp only [map_zero, Function.const_zero]
  apply Matrix.eq_zero_of_mulVec_eq_zero hb
  ext i
  apply i.injective
  unfold M
  simp only [Matrix.mulVec_eq_sum, Function.comp_apply, op_smul_eq_smul, algebraMap_smul,
    Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    map_sum, MvPolynomial.smul_eval, MvPolynomial.eval_X, map_smul, map_mul,
    AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Pi.zero_apply, map_zero]
  rw [← ha, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun i => zero_smul K (i _)]
  simp_rw [map_sum, map_smul, Algebra.smul_def, mul_comm]

theorem exists_linearIndependent_algEquiv_apply :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ x := by
  obtain h | h := finite_or_infinite K
  · have := Module.finite_of_finite K (M := L)
    exact exists_linearIndependent_algEquiv_apply_of_finite K L
  · exact exists_linearIndependent_algEquiv_apply_of_infinite K L

namespace IsGalois

variable [IsGalois K L]

/-- Given a finite Galois extension `L/K`, `normalBasis K L` is a basis of `L` over `K`
that is an orbit under the Galois group action. -/
noncomputable def normalBasis : Basis (L ≃ₐ[K] L) K L :=
  basisOfLinearIndependentOfCardEqFinrank
    (exists_linearIndependent_algEquiv_apply K L).choose_spec
    (card_aut_eq_finrank K L)

variable {K L}

theorem normalBasis_apply (e : L ≃ₐ[K] L) : normalBasis K L e = e (normalBasis K L 1) := by
  rw [normalBasis, coe_basisOfLinearIndependentOfCardEqFinrank, AlgEquiv.one_apply]

end IsGalois
