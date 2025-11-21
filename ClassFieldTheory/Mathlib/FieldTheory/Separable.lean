import Mathlib.FieldTheory.Separable

theorem Algebra.IsSeparable.iff_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*}
    [Field A₁] [Ring B₁] [Field A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁ = (e₂ : B₁ →+* B₂).comp (algebraMap A₁ B₁)) :
    Algebra.IsSeparable A₁ B₁ ↔ Algebra.IsSeparable A₂ B₂ :=
  ⟨(·.of_equiv_equiv e₁ e₂ he), (·.of_equiv_equiv e₁.symm e₂.symm <| by
    rw [← (algebraMap A₂ B₂).comp_id, ← RingEquiv.comp_symm e₁, ← RingHom.comp_assoc,
      ← RingHom.comp_assoc, RingHom.comp_assoc _ (algebraMap A₂ B₂), he,
      ← RingHom.comp_assoc, e₂.symm_comp, RingHom.id_comp])⟩

open Polynomial

theorem Polynomial.nodup_nthRoots_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {a : R} (hn : (n : R) ≠ 0) (ha : a ≠ 0) : (nthRoots n a).Nodup := by
  have : (⇑(algebraMap R (FractionRing R))).Injective := FaithfulSMul.algebraMap_injective ..
  rw [nthRoots, ← Multiset.nodup_map_iff_of_injective this]
  refine Multiset.nodup_of_le (map_roots_le_of_injective _ this) ?_
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  refine nodup_roots <| separable_X_pow_sub_C _ ?_ (map_ne_zero_iff _ this |>.mpr ha)
  · rw [← map_natCast (algebraMap R _)]
    exact map_ne_zero_iff _ this |>.mpr hn

theorem Polynomial.nodup_nthRoots_one_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : (n : R) ≠ 0) : (nthRoots n (1 : R)).Nodup :=
  nodup_nthRoots_of_natCast_ne_zero hn one_ne_zero
