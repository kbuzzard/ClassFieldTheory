import Mathlib.RingTheory.Nilpotent.Lemmas

-- forward direction of `Ideal.FG.isNilpotent_iff_le_nilradical`
theorem le_nilradical_of_isNilpotent {R : Type*} [CommSemiring R] {I : Ideal R}
    (hi : IsNilpotent I) : I ≤ nilradical R :=
  fun _ hx ↦ hi.rec fun n hn ↦ ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩
