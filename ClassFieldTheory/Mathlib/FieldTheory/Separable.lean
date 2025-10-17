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
