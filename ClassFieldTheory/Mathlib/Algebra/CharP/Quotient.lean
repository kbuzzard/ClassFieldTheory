import Mathlib.Algebra.CharP.Quotient

theorem CharP.mem {R : Type*} [CommRing R] (p : ℕ) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp <| by simp
