/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Mathlib.RingTheory.LiftingCoprime
import ClassFieldTheory.Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Hensel's lemma on factorisation of polynomials

If `(R, I, R/I)` is Henselian then any monic irreducible separable polynomial in `R` is also
irreducible in `R/I`.

## Implementation details

We introduce an auxiliary object `MonicCoprimeFactors f` which is the pairs `(p, q)` such that
`p * q = f` and `p` and `q` are monic and coprime.

* We show that the map on such factorisations induced by `φ : R →+* S` is bijective whenever
  `φ` is surjective with kernel being square-zero. (Equivalently, `R →+* R ⧸ I` for a square-zero
  ideal `I`.)
* This then implies the same with just nilpotent kernel.
* Then if `R ≃ lim (R⧸I^n)` then this allows you to lift factorisations in `R⧸I` to factorisations
  in `R`.

-/

section Lemmas

open Polynomial

/-- If `R →+* S` is surjective then a monic `S[X]` can be lifted to a monic `R[X]`. -/
theorem Polynomial.exists_monic_map {R S : Type*} [Semiring R] [Semiring S]
    {f : R →+* S} (hf : (⇑f).Surjective) {y : S[X]} (hy : y.Monic) :
    ∃ x : R[X], x.Monic ∧ x.map f = y := by
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  refine ⟨X ^ y.natDegree + ∑ i : Fin y.natDegree, C (g (y.coeff i)) * X ^ i.1,
    monic_X_pow_add <| degree_sum_fin_lt _,
    by simpa [Polynomial.map_sum, hg _, Finset.sum_range] using hy.as_sum.symm⟩

open Ideal Quotient

theorem Ideal.Quotient.ker_factorPow_pow {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ}
    (le : m ≤ n) (hm : m ≠ 0) : RingHom.ker (factorPow I le) ^ n = ⊥ := by
  rw [factorPow, factor_ker, ← Ideal.map_pow, ← pow_mul,
    Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right <| Nat.le_mul_of_pos_left _ <| by grind)]

theorem IsNilpotent.ker_factorPow {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (le : m ≤ n)
    (hm : m ≠ 0) : IsNilpotent (RingHom.ker (factorPow I le)) :=
  ⟨n, by simpa using ker_factorPow_pow I le hm⟩

theorem Ideal.map_le_nilradical {R S : Type*} [CommSemiring R] [CommSemiring S] {I : Ideal R}
    (h : I ≤ nilradical R) {f : R →+* S} : I.map f ≤ nilradical S :=
  map_le_of_le_comap fun _ hx ↦ IsNilpotent.map (h hx) _

/-- If `p ∈ I[X]` then `p /ₘ q ∈ I[X]`. -/
theorem Polynomial.divByMonic_mem_map {R : Type*} [CommRing R] {I : Ideal R} {p q : R[X]}
    (hp : p ∈ I.map C) : p /ₘ q ∈ I.map C := by
  rw [← mk_ker (I := I), ← ker_mapRingHom, RingHom.mem_ker, coe_mapRingHom] at hp ⊢
  by_cases hq : q.Monic
  · rw [map_divByMonic _ hq, hp, zero_divByMonic]
  · rw [divByMonic_eq_of_not_monic _ hq, Polynomial.map_zero]

/-- If `p ∈ I[X]` then `p %ₘ q ∈ I[X]`. -/
theorem Polynomial.modByMonic_mem_map {R : Type*} [CommRing R] {I : Ideal R} {p q : R[X]}
    (hp : p ∈ I.map C) : p %ₘ q ∈ I.map C := by
  rw [← mk_ker (I := I), ← ker_mapRingHom, RingHom.mem_ker, coe_mapRingHom] at hp ⊢
  by_cases hq : q.Monic
  · rw [map_modByMonic _ hq, hp, zero_modByMonic]
  · rw [modByMonic_eq_of_not_monic _ hq, hp]

theorem Polynomial.degree_add_lt {R : Type*} [Semiring R] {p q : R[X]} {n}
    (hp : p.degree < n) (hq : q.degree < n) : (p + q).degree < n :=
  (degree_add_le _ _).trans_lt <| max_lt hp hq

theorem Polynomial.degree_sub_lt' {R : Type*} [Ring R] {p q : R[X]} {n}
    (hp : p.degree < n) (hq : q.degree < n) : (p - q).degree < n :=
  degree_add_lt hp <| degree_neg q ▸ hq

theorem Polynomial.Monic.degree_mul' {R : Type*} [Semiring R] {p q : Polynomial R} (hp : p.Monic) :
    (p * q).degree = p.degree + q.degree := by
  rw [hp.degree_mul_comm, hp.degree_mul, add_comm]

end Lemmas


open Ideal Quotient

namespace Polynomial
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- `(p, q)` such that `pq = f`, and `p` and `q` are monic and coprime. -/
@[ext] structure MonicCoprimeFactors (f : R[X]) where
  /-- The first factor. -/
  fst : R[X]
  /-- The second factor. -/
  snd : R[X]
  monic_fst : Monic fst
  monic_snd : Monic snd
  coprime_fst_snd : IsCoprime fst snd
  fst_mul_snd_eq : fst * snd = f

variable {f g : R[X]} {I J : Ideal R}

namespace MonicCoprimeFactors

theorem monic (fac : MonicCoprimeFactors f) : f.Monic :=
  fac.6 ▸ fac.3.mul fac.4

/-- Functoriality. -/
@[simps!] noncomputable def map
    (φ : R →+* S) (fac : MonicCoprimeFactors f) : MonicCoprimeFactors (map φ f) where
  fst := fac.fst.map φ
  snd := fac.snd.map φ
  monic_fst := fac.3.map _
  monic_snd := fac.4.map _
  coprime_fst_snd := fac.5.map (mapRingHom φ)
  fst_mul_snd_eq := by rw [← Polynomial.map_mul, fac.6]

/-- Dependent type issues -/
@[simps!] noncomputable def congr (h : f = g) : MonicCoprimeFactors f ≃ MonicCoprimeFactors g where
  toFun fac := ⟨fac.1, fac.2, fac.3, fac.4, fac.5, h ▸ fac.6⟩
  invFun fac := ⟨fac.1, fac.2, fac.3, fac.4, fac.5, h ▸ fac.6⟩

theorem map_id : map (.id R) (f := f) = congr (by simp) := by
  ext <;> simp

theorem map_comp (φ : S →+* T) (ψ : R →+* S) :
    map (φ.comp ψ) (f := f) = congr (by simp [map_map]) ∘ map φ ∘ map ψ := by
  ext <;> simp

/-- If `e : R ≃+* S` then `MonicCoprimeFactors f ≃ MonicCoprimeFactors (e f)`. -/
@[simps!] noncomputable def mapEquiv (e : R ≃+* S) :
    MonicCoprimeFactors f ≃ MonicCoprimeFactors (f.map (e : R →+* S)) where
  toFun := map (e : R →+* S)
  invFun := congr (by simp [map_map]) ∘ map (e.symm : S →+* R)
  left_inv fac := by ext <;> simp
  right_inv fac := by ext <;> simp

noncomputable instance [Subsingleton R] : Unique (MonicCoprimeFactors f) where
  default := ⟨1, 1, by simp, by simp, isCoprime_one_left, by subsingleton⟩
  uniq _ := by ext <;> subsingleton

section
variable [Nontrivial S] {fac : MonicCoprimeFactors f} (φ : R →+* S)

/-- Degree is preserved by `map`. -/
theorem degree_fst_map  : (fac.map φ).fst.degree = fac.fst.degree :=
  fac.3.degree_map _

/-- Degree is preserved by `map`. -/
theorem degree_snd_map  : (fac.map φ).snd.degree = fac.snd.degree :=
  fac.4.degree_map _

/-- Degree is preserved by `map`. -/
theorem natDegree_fst_map  : (fac.map φ).fst.natDegree = fac.fst.natDegree :=
  fac.3.natDegree_map _

/-- Degree is preserved by `map`. -/
theorem natDegree_snd_map  : (fac.map φ).snd.natDegree = fac.snd.natDegree :=
  fac.4.natDegree_map _

end

variable (f) (I : Ideal R) (hi : I ^ 2 = ⊥)
include hi

/-- Monic coprime factorisations in `R` injects into those in `R ⧸ I` if `I ^ 2 = ⊥`. -/
theorem map_injective_of_sqZero : (map (Ideal.Quotient.mk I) (f := f)).Injective := by
  -- Suppose we have factorisations `f = p * q = r * s` in `R[X]`.
  intro fac₁ fac₂ eq
  -- WLOG `R ⧸ I` is nontrivial
  obtain hr | hr := subsingleton_or_nontrivial (R ⧸ I)
  · rw [Ideal.Quotient.subsingleton_iff] at hr
    rw [hr, top_pow, eq_comm, subsingleton_iff_bot_eq_top, Submodule.subsingleton_iff] at hi
    subsingleton
  have := (Ideal.Quotient.mk I).domain_nontrivial
  -- -- `deg q = deg s`
  have h₂ : fac₁.snd.degree = fac₂.snd.degree := by
    convert congr($eq.2.degree) using 1 <;>
    simp only [degree_snd_map]
  have h₃ : fac₁.snd.natDegree = fac₂.snd.natDegree := natDegree_eq_natDegree h₂
  obtain ⟨p, q, mp, mq, c₁, e₁⟩ := fac₁
  obtain ⟨r, s, mr, ms, c₂, e₂⟩ := fac₂
  have h₁ : p * q = r * s := e₁.trans e₂.symm
  -- Then `p - r ∈ I[X]` and `q - s ∈ I[X]`, so `(p - r) * (q - s) = 0`.
  simp_rw [MonicCoprimeFactors.ext_iff, map_fst, map_snd, ← coe_mapRingHom,
    ← RingHom.sub_mem_ker_iff, ker_mapRingHom] at eq
  replace eq := mul_mem_mul eq.1 eq.2
  rw [← Ideal.map_mul, mk_ker, ← sq, hi, Ideal.map_bot, mem_bot] at eq
  -- Then by coprime let `a, b` with `a * p + b * q = 1`.
  obtain ⟨a, b, hab⟩ := c₁
  -- Then `q - s = q * (b * (q - s) - a * (p - r))`.
  have := calc
        q - s
      = (a * p + b * q) * (q - s) - a * (p * q - r * s) - a * (p - r) * (q - s) :=
        by simp [hab, h₁, mul_assoc, eq]
    _ = q * (b * (q - s) - a * (p - r)) := by ring
  -- which means `q ∣ q - s`, but `q` is monic and `s` is monic and `q` and `s` have same degree
  have h₃ : (q - s).degree < q.degree := degree_sub_lt h₂ mq.ne_zero (by simp [*])
  -- therefore `q - s = 0`
  have h₄ : q = s := sub_eq_zero.mp <| by_contra (mq.not_dvd_of_degree_lt · h₃ ⟨_, this⟩)
  subst h₄
  -- therefore `p = r`
  obtain rfl := mq.isRegular.right h₁
  rfl

/-- Monic coprime factorisations in `R` surjects onto those in `R ⧸ I` if `I ^ 2 = ⊥`. -/
theorem map_surjective_of_sqZero (hmf : f.Monic) :
    (map (Ideal.Quotient.mk I) (f := f)).Surjective := by
  -- WLOG `R ⧸ I` is nontrivial
  obtain hr | hr := subsingleton_or_nontrivial (R ⧸ I)
  · rw [Ideal.Quotient.subsingleton_iff] at hr
    rw [hr, top_pow, eq_comm, subsingleton_iff_bot_eq_top, Submodule.subsingleton_iff] at hi
    exact Function.surjective_to_subsingleton _
  have := (Ideal.Quotient.mk I).domain_nontrivial
  let φ := Ideal.Quotient.mk I
  have hφ : RingHom.ker (mapRingHom φ) = Ideal.map C I := by rw [ker_mapRingHom, mk_ker]
  have hφ2 : RingHom.ker (mapRingHom φ) * RingHom.ker (mapRingHom φ) = ⊥ := by
    rw [hφ, ← Ideal.map_mul, ← sq, hi, Ideal.map_bot]
  rintro ⟨p, q, mp', mq', cpq, hpq⟩
  have h₁ : (⇑φ).Surjective := mk''_surjective
  obtain ⟨p, mp, rfl⟩ := p.exists_monic_map h₁ mp'
  obtain ⟨q, mq, rfl⟩ := q.exists_monic_map h₁ mq'
  obtain ⟨a, b, hab⟩ := cpq.of_map (mapRingHom φ) (map_surjective _ h₁) <| by
    exact le_nilradical_of_isNilpotent ⟨2, by rw [sq (RingHom.ker _), hφ2, bot_eq_zero]⟩
  -- a(f-pq) = qr+s
  let r := a * (f - p * q) /ₘ q
  let s := a * (f - p * q) %ₘ q
  have hrs : a * (f - p * q) = s + q * r := (modByMonic_add_div _ mq).symm
  -- b(f-pq) = pt+u
  let t := b * (f - p * q) /ₘ p
  let u := b * (f - p * q) %ₘ p
  have htu : b * (f - p * q) = u + p * t := (modByMonic_add_div _ mp).symm
  have hfpq : f - p * q ∈ RingHom.ker (mapRingHom φ) := by simp [hpq, φ]
  have hs : s ∈ RingHom.ker (mapRingHom φ) :=
    hφ ▸ (modByMonic_mem_map <| mul_mem_left _ _ <| hφ ▸ hfpq)
  have hu : u ∈ RingHom.ker (mapRingHom φ) :=
    hφ ▸ (modByMonic_mem_map <| mul_mem_left _ _ <| hφ ▸ hfpq)
  have hsu : s * u = 0 := by
    rw [← mem_bot, ← hφ2]
    exact mul_mem_mul hs hu
  simp only [RingHom.mem_ker, coe_mapRingHom] at hs hu
  -- then pq(r+t) = (f-pq) - (ps+qu)
  have key := calc
        p * q * (r + t)
      = p * (s + q * r) + q * (u + p * t) - (p * s + q * u) := by ring
    _ = (a * p + b * q) * (f - p * q) - (p * s + q * u) := by rw [← hrs, ← htu]; ring
    _ = (f - p * q) - (p * s + q * u) := by rw [hab, one_mul]
  -- pq is monic with deg f; and the RHS is < deg f, therefore RHS = 0
  let n := f.natDegree
  have hpqn' : (p * q).natDegree = n := by
    rw [← (mp.mul mq).natDegree_map φ, Polynomial.map_mul, hpq, hmf.natDegree_map]
  have hpqn : p.natDegree + q.natDegree = n := by rw [← mp.natDegree_mul mq, hpqn']
  have hdf : f.degree = n := degree_eq_natDegree hmf.ne_zero
  have hdpq : p.degree + q.degree = n := by
    rw [← mq.degree_mul]; exact (degree_eq_iff_natDegree_eq (mp.mul mq |>.ne_zero)).mpr hpqn'
  have h₂ : (f - p * q).degree < f.degree :=
    degree_sub_lt (hdf ▸ .symm ((degree_eq_iff_natDegree_eq (mp.mul mq |>.ne_zero)).mpr hpqn'))
      (hmf.ne_zero) (by rw [hmf, mp.mul mq])
  have h₃ : (p * s + q * u).degree < p.degree + q.degree := by
    refine degree_add_lt ?_ ?_
    · rw [mp.degree_mul']
      exact WithBot.add_lt_add_left (by simpa using mp.ne_zero) (degree_modByMonic_lt _ mq)
    · rw [mul_comm q, mq.degree_mul]
      exact WithBot.add_lt_add_right (by simpa using mq.ne_zero) (degree_modByMonic_lt _ mp)
  have h₄ := degree_sub_lt' (hdf ▸ h₂) (hdpq ▸ h₃)
  have h₅ : f - p * q - (p * s + q * u) = 0 := by_contra fun h ↦ by
    have := (natDegree_lt_iff_degree_lt h).mpr h₄
    rw [← key, ← hpqn', (mp.mul mq).mul_natDegree_lt_iff] at this
    exact h <| key ▸ by simp [this.2]
  rw [← hsu, sub_eq_iff_eq_add, sub_eq_iff_eq_add] at h₅
  replace h₅ : f = (p + u) * (q + s) := by rw [h₅]; ring
  refine ⟨⟨p + u, q + s, mp.add_of_left (degree_modByMonic_lt _ mp),
    mq.add_of_left (degree_modByMonic_lt _ mq), ?_, h₅.symm⟩, ?_⟩
  · exact .of_map (mapRingHom φ) (map_surjective _ h₁)
      (le_nilradical_of_isNilpotent ⟨2, by simpa [sq] using hφ2⟩)
      (by simpa [hs, hu])
  · ext : 1
    · change (p + u).map φ = p.map φ; simp [hu]
    · change (q + s).map φ = q.map φ; simp [hs]

/-- Monic coprime factorisations in `R` bijects onto those in `R ⧸ I` if `I ^ 2 = ⊥`. -/
theorem map_bijective_of_sqZero (hmf : f.Monic) :
    (map (Ideal.Quotient.mk I) (f := f)).Bijective :=
  ⟨map_injective_of_sqZero f I hi, map_surjective_of_sqZero f I hi hmf⟩

end MonicCoprimeFactors

end Polynomial

#check AdicCompletion.ofLinearEquiv

#min_imports
#lint
