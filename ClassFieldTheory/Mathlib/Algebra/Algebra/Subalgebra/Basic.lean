import Mathlib.Algebra.Algebra.Subalgebra.Basic

instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ) :
    Algebra s R :=
  (SubringClass.subtype s).toAlgebra

@[simp] theorem SubringClass.coe_algebraMap {R : Type*} [CommRing R] {σ : Type*}
    [SetLike σ R] [SubringClass σ R] (s : σ) : ⇑(algebraMap s R) = Subtype.val := rfl
