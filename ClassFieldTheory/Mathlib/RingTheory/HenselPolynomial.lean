/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Mathlib.RingTheory.AdicCompletion.Ring
import ClassFieldTheory.Mathlib.RingTheory.LiftingCoprime
import ClassFieldTheory.Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.FieldTheory.Separable

/-! # Hensel's lemma on factorisation of polynomials

If `(R, I, R/I)` is Henselian then any monic irreducible separable polynomial in `R` is also
irreducible in `R/I`.

## Implementation details

* We introduce an auxiliary object `MonicCoprimeFactors f` which is the pairs `(p, q)` such that
  `p * q = f` and `p` and `q` are monic and coprime.
* We show that the map on such factorisations induced by `φ : R →+* S` is bijective whenever
  `φ` is surjective with square-zero kernel. (Equivalently, `R →+* R ⧸ I` for a square-zero
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

theorem IsNilpotent.ker_factor {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    IsNilpotent (RingHom.ker (factor (I.pow_le_self hn))) :=
  ⟨n, by rw [factor_ker, ← Ideal.map_pow, map_quotient_self, zero_eq_bot]⟩

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

section
variable {R S : Type*} [Ring R] [Semiring S] {f : R →+* S} (hf : Function.Surjective ⇑f)

theorem RingHom.quotientKerEquivOfSurjective_comp :
    (RingHom.quotientKerEquivOfSurjective hf : _ →+* _).comp (Ideal.Quotient.mk (ker f)) = f := rfl

theorem RingHom.quotientKerEquivOfSurjective_symm_comp :
    ((RingHom.quotientKerEquivOfSurjective hf).symm : _ →+* _).comp f =
    Ideal.Quotient.mk (ker f) := by
  conv => enter [1,2]; rw [← quotientKerEquivOfSurjective_comp hf]
  rw [← comp_assoc, RingEquiv.symm_comp, id_comp]

end

end Lemmas

open Ideal Quotient

namespace Polynomial
variable {R S T : Type*}

/-- `(p, q)` such that `pq = f`, and `p` and `q` are monic. -/
@[ext] structure MonicFactors [Semiring R] (f : R[X]) where
  /-- The first factor. -/
  fst : R[X]
  /-- The second factor. -/
  snd : R[X]
  monic_fst : Monic fst
  monic_snd : Monic snd
  fst_mul_snd_eq : fst * snd = f

namespace MonicFactors
variable [Semiring R] [Semiring S]

/-- Functoriality. -/
@[simps!] noncomputable def map
    {f : R[X]} (φ : R →+* S) (fac : MonicFactors f) : MonicFactors (f.map φ) where
  fst := fac.fst.map φ
  snd := fac.snd.map φ
  monic_fst := fac.3.map _
  monic_snd := fac.4.map _
  fst_mul_snd_eq := by rw [← Polynomial.map_mul, fac.5]

/-- The first trivial factoring, where `f = 1 * f`. -/
@[simps!] noncomputable def fstOne {f : R[X]} (mf : f.Monic) : MonicFactors f where
  fst := 1
  snd := f
  monic_fst := monic_one
  monic_snd := mf
  fst_mul_snd_eq := one_mul f

/-- The first trivial factoring, where `f = 1 * f`. -/
@[simps!] noncomputable def sndOne {f : R[X]} (mf : f.Monic) : MonicFactors f where
  fst := f
  snd := 1
  monic_fst := mf
  monic_snd := monic_one
  fst_mul_snd_eq := mul_one f

theorem fstOne_eq_sndOne_iff {f : R[X]} {mf : f.Monic} : fstOne mf = sndOne mf ↔ f = 1 :=
  ⟨fun h ↦ congr(($h).2), fun h ↦ by subst h; rfl⟩

noncomputable instance [Subsingleton R] (f : R[X]) :
    Unique (MonicFactors f) where
  default := fstOne f.monic_of_subsingleton
  uniq _ := MonicFactors.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end MonicFactors

/-- `(p, q)` such that `pq = f`, and `p` and `q` are monic and coprime. -/
@[ext] structure MonicCoprimeFactors [CommSemiring R] (f : R[X]) where
  /-- The first factor. -/
  fst : R[X]
  /-- The second factor. -/
  snd : R[X]
  monic_fst : Monic fst
  monic_snd : Monic snd
  coprime_fst_snd : IsCoprime fst snd
  fst_mul_snd_eq : fst * snd = f

namespace MonicCoprimeFactors

section CommSemiring
variable [CommSemiring R] [CommSemiring S] [CommSemiring T] {f g : R[X]} {I J : Ideal R}

/-- Forgetting coprimality. -/
@[simps!] def toMonicFactors (fac : MonicCoprimeFactors f) : MonicFactors f where
  fst := fac.fst
  snd := fac.snd
  monic_fst := fac.3
  monic_snd := fac.4
  fst_mul_snd_eq := fac.6

theorem toMonicFactors_injective : (toMonicFactors (f := f)).Injective :=
  fun _ _ eq ↦ MonicCoprimeFactors.ext congr(($eq).fst) congr(($eq).snd)

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

theorem congr_symm (h : f = g) : (congr h).symm = congr h.symm := rfl

theorem congr_trans {f₁ f₂ f₃ : R[X]} (h1 : f₁ = f₂) (h2 : f₂ = f₃) :
    (congr h1).trans (congr h2) = congr (h1.trans h2) := rfl

theorem congr_rfl : congr (rfl : f = f) = .refl _ := rfl

theorem map_congr (φ : R →+* S) (h : f = g) : map φ ∘ congr h = congr (by rw [h]) ∘ map φ := rfl

theorem map_id : map (.id R) (f := f) = congr (by simp) := by ext <;> simp

theorem map_comp (φ : S →+* T) (ψ : R →+* S) :
    map (φ.comp ψ) (f := f) = congr (by simp [map_map]) ∘ map φ ∘ map ψ := by ext <;> simp

theorem map_comp_map (φ : S →+* T) (ψ : R →+* S) :
    map φ ∘ map ψ = congr (by simp [map_map]) ∘ map (φ.comp ψ) (f := f) := by ext <;> simp

/-- If `e : R ≃+* S` then `MonicCoprimeFactors f ≃ MonicCoprimeFactors (e f)`. -/
@[simps!] noncomputable def mapEquiv (e : R ≃+* S) :
    MonicCoprimeFactors f ≃ MonicCoprimeFactors (f.map (e : R →+* S)) where
  toFun := map (e : R →+* S)
  invFun := congr (by simp [map_map]) ∘ map (e.symm : S →+* R)
  left_inv fac := by ext <;> simp
  right_inv fac := by ext <;> simp

@[simp] lemma coe_mapEquiv (e : R ≃+* S) : ⇑(mapEquiv e (f := f)) = map (e : R →+* S) := rfl

@[simp] lemma coe_mapEquiv_symm (e : R ≃+* S) :
    ⇑(mapEquiv e (f := f)).symm = congr (by simp [map_map]) ∘ map (e.symm : S →+* R) := rfl

/-- The first trivial factoring, where `f = 1 * f`. -/
@[simps!] noncomputable def fstOne (mf : f.Monic) : MonicCoprimeFactors f where
  fst := 1
  snd := f
  monic_fst := monic_one
  monic_snd := mf
  coprime_fst_snd := isCoprime_one_left
  fst_mul_snd_eq := one_mul f

/-- Swapping the two factors -/
@[simps!] noncomputable def swap (fac : MonicCoprimeFactors f) : MonicCoprimeFactors f where
  fst := fac.snd
  snd := fac.fst
  monic_fst := fac.4
  monic_snd := fac.3
  coprime_fst_snd := fac.5.symm
  fst_mul_snd_eq := mul_comm fac.snd fac.fst ▸ fac.6

/-- The second trivial factoring, where `f = f * 1`. -/
@[simps!] noncomputable def sndOne (mf : f.Monic) : MonicCoprimeFactors f := (fstOne mf).swap

theorem fstOne_eq_sndOne_iff {f : R[X]} {mf : f.Monic} : fstOne mf = sndOne mf ↔ f = 1 :=
  ⟨fun h ↦ congr(($h).2), fun h ↦ by subst h; rfl⟩

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
end CommSemiring

variable [CommRing R] [CommRing S] (f : R[X]) (I : Ideal R) (hi : I ^ 2 = ⊥)

include hi in
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

include hi in
/-- Monic coprime factorisations in `R` surjects onto those in `R ⧸ I` if `I ^ 2 = ⊥`. -/
theorem map_surjective_of_sqZero (mf : f.Monic) :
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
  have := IsLocalHom.of_ker_le_nilradical (mapRingHom φ) (map_surjective _ mk''_surjective) <| by
    exact le_nilradical_of_isNilpotent ⟨2, by rw [sq, hφ2, zero_eq_bot]⟩
  obtain ⟨a, b, hab⟩ := cpq.of_map (mapRingHom φ) (map_surjective _ h₁)
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
    rw [← (mp.mul mq).natDegree_map φ, Polynomial.map_mul, hpq, mf.natDegree_map]
  have hpqn : p.natDegree + q.natDegree = n := by rw [← mp.natDegree_mul mq, hpqn']
  have hdf : f.degree = n := degree_eq_natDegree mf.ne_zero
  have hdpq : p.degree + q.degree = n := by
    rw [← mq.degree_mul]; exact (degree_eq_iff_natDegree_eq (mp.mul mq |>.ne_zero)).mpr hpqn'
  have h₂ : (f - p * q).degree < f.degree :=
    degree_sub_lt (hdf ▸ .symm ((degree_eq_iff_natDegree_eq (mp.mul mq |>.ne_zero)).mpr hpqn'))
      (mf.ne_zero) (by rw [mf, mp.mul mq])
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
  · exact .of_map (mapRingHom φ) (map_surjective _ h₁) (by simpa [hs, hu])
  · ext : 1
    · change (p + u).map φ = p.map φ; simp [hu]
    · change (q + s).map φ = q.map φ; simp [hs]

include hi in
/-- Monic coprime factorisations in `R` bijects onto those in `R ⧸ I` if `I ^ 2 = ⊥`. -/
theorem map_bijective_of_sqZero (mf : f.Monic) :
    (map (Ideal.Quotient.mk I) (f := f)).Bijective :=
  ⟨map_injective_of_sqZero f I hi, map_surjective_of_sqZero f I hi mf⟩

variable (φ : R →+* S) (hφ : (⇑φ).Surjective)

include hφ in
/-- `R →+* S` surjective with square-zero kernel induces a bijection between factorisations. -/
theorem map_bijective_of_sqZero_ker (hφ2 : RingHom.ker φ ^ 2 = ⊥) (mf : f.Monic) :
    (map φ (f := f)).Bijective :=
  (Equiv.comp_bijective _ <| mapEquiv (RingHom.quotientKerEquivOfSurjective hφ).symm).mp <| by
    rw [coe_mapEquiv, map_comp_map, Equiv.comp_bijective,
    RingHom.quotientKerEquivOfSurjective_symm_comp]
    exact map_bijective_of_sqZero f (RingHom.ker φ) hφ2 mf

/-- Monic coprime factorisations in `R` bijects onto those in `R ⧸ I` if `I ^ n = ⊥`. -/
theorem map_bijective_of_isNilpotent (hi : IsNilpotent I) (mf : f.Monic) :
    (map (Ideal.Quotient.mk I) (f := f)).Bijective := by
  obtain ⟨n, hn⟩ := hi
  rw [zero_eq_bot, eq_bot_iff] at hn
  induction n using Nat.strongRec generalizing I with
  | ind n ih =>
    obtain hn1 | h1n := le_or_gt n 1
    · replace hn := (pow_le_pow_right hn1).trans hn
      rw [pow_one, le_bot_iff] at hn; subst hn
      exact (mapEquiv <| (RingEquiv.quotientBot R).symm).bijective
    change (map ((factor (Ideal.pow_le_self two_ne_zero)).comp
      (Ideal.Quotient.mk (I ^ 2))) (f := f)).Bijective
    rw [map_comp, Equiv.comp_bijective]
    exact .comp (map_bijective_of_sqZero_ker _ _ (factor_surjective _)
      (by rw [factor_ker, ← Ideal.map_pow, map_quotient_self]) (mf.map _))
      (ih (n - 1) (by omega) _ <| by rw [← pow_mul]; exact (pow_le_pow_right (by omega)).trans hn)

include hφ in
/-- `R →+* S` surjective with nilpotent kernel induces a bijection between factorisations. -/
theorem map_bijective_of_isNilpotent_ker (hφ0 : IsNilpotent (RingHom.ker φ)) (mf : f.Monic) :
    (map φ (f := f)).Bijective :=
  (Equiv.comp_bijective _ <| mapEquiv (RingHom.quotientKerEquivOfSurjective hφ).symm).mp <| by
    rw [coe_mapEquiv, map_comp_map, Equiv.comp_bijective,
    RingHom.quotientKerEquivOfSurjective_symm_comp]
    exact map_bijective_of_isNilpotent f (RingHom.ker φ) hφ0 mf

variable {f : R[X]} {mf : f.Monic} {n : ℕ}

/-- `R ⧸ I ^ (n + 1) →+* R ⧸ I` induces a bijection between factorisations. -/
noncomputable def liftFactorPow (mf : f.Monic) {n : ℕ} :
    MonicCoprimeFactors (f.map (Ideal.Quotient.mk (I ^ (n + 1)))) ≃
    MonicCoprimeFactors (f.map (Ideal.Quotient.mk I)) :=
  .trans (.ofBijective (_) <| map_bijective_of_isNilpotent_ker _ (factor (I.pow_le_self (by grind)))
    (factor_surjective _) (.ker_factor _ (by grind)) (mf.map _)) (congr <| by simp [map_map])

@[simp] theorem coe_liftFactorPow {n : ℕ} : ⇑(liftFactorPow I mf (n := n)) =
      congr (by simp [map_map]) ∘ map (factor (I.pow_le_self (by grind))) := rfl

lemma liftFactorPow_fst {fac} :
    (liftFactorPow I mf (n := n) fac).fst = (map (factor (I.pow_le_self (by grind))) fac).fst :=
  rfl

lemma liftFactorPow_snd {fac} :
    (liftFactorPow I mf (n := n) fac).snd = (map (factor (I.pow_le_self (by grind))) fac).snd :=
  rfl

theorem map_factorPowSucc_liftFactorPow :
    map (factorPowSucc I (n + 1)) ∘ (liftFactorPow I mf).symm =
      congr (by simp [map_map]) ∘ ((liftFactorPow I mf).symm) := by
  rw [Equiv.comp_symm_eq, Function.comp_assoc, ← Equiv.symm_comp_eq, Equiv.eq_symm_comp]
  ext fac : 2 <;> simp [map_map]

theorem fst_map_factorPowSucc_liftFactorPow {fac} :
    (map (factorPowSucc I (n + 1)) ((liftFactorPow I mf).symm fac)).fst =
      ((liftFactorPow I mf).symm fac).fst := by
  rw [← Function.comp_apply (f := map _), map_factorPowSucc_liftFactorPow]; rfl

theorem snd_map_factorPowSucc_liftFactorPow {mf : f.Monic} {n : ℕ} {fac} :
    (map (factorPowSucc I (n + 1)) ((liftFactorPow I mf).symm fac)).snd =
      ((liftFactorPow I mf).symm fac).snd := by
  rw [← Function.comp_apply (f := map _), map_factorPowSucc_liftFactorPow]; rfl

variable {I : Ideal R} [IsAdicComplete I R]

open AdicCompletion

-- generalises `isUnit_iff_notMem_of_isAdicComplete_maximal`
instance : IsLocalHom (Ideal.Quotient.mk I) := by
  rw [isLocalHom_iff_one mk_surjective]
  intro x hx
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ I, x = 1 - r := ⟨1 - x, by simp [← Ideal.Quotient.eq, hx], by simp⟩
  -- would be shorter with adic expansion
  have : IsAdicCauchy I R fun n ↦ ∑ i ∈ Finset.range n, r ^ i := by
    rw [isAdicCauchy_iff]
    intro n
    rw [Finset.sum_range_succ, SModEq, eq_comm, Submodule.Quotient.eq, add_sub_cancel_left,
      smul_eq_mul, mul_top]
    exact Ideal.pow_mem_pow hr _
  refine isUnit_iff_exists_inv.mpr ⟨(ofLinearEquiv I R).symm <| .mk _ _ ⟨_, this⟩, ?_⟩
  generalize hy : (ofLinearEquiv I R).symm _ = y
  simp_rw [LinearEquiv.symm_apply_eq, ofLinearEquiv_apply, AdicCompletion.ext_iff, of_apply,
    AdicCompletion.mk_apply_coe, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk] at hy
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
  simp_rw [SModEq, Ideal.Quotient.mk_eq_mk, map_mul, ← hy, ← map_mul, Ideal.Quotient.eq,
    mul_neg_geom_sum, sub_sub_cancel_left, smul_eq_mul, mul_top, neg_mem_iff]
  exact Ideal.pow_mem_pow hr _

/-- A sequence of monic polynomials in `(R ⧸ I ^ n)[X]` that maps to each other has a limit. -/
noncomputable def _root_.Polynomial.limit (f : ∀ n, (R ⧸ I ^ n)[X])
    (hf : ∀n, (f (n + 1)).map (factorPowSucc I n) = f n) : R[X] :=
  ∑ i ∈ Finset.range ((f 1).natDegree + 1), C ((ofLinearEquiv I R).symm <| .mkRing
    (fun n ↦ (f n).coeff i) fun n ↦ by simpa using congr($(hf n).coeff i)) * X ^ i

/-- For a polynomial given explicitly as `∑ i, C (f i) * X ^ i`, the `i`-th coefficient is `f i`. -/
theorem _root_.Polynomial.coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} {f : ℕ → R}
    {i : ℕ} : (∑ i ∈ Finset.range n, C (f i) * X ^ i).coeff i = if i < n then f i else 0 := by
  simp_rw [← lcoeff_apply, map_sum, lcoeff_apply, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem i (by simpa) (by grind), if_pos rfl]
  · exact Finset.sum_eq_zero (fun x hx ↦ if_neg (by grind))

theorem _root_.Polynomial.map_limit {f : ∀ n, (R ⧸ I ^ n)[X]} {hf} {n : ℕ}
    (mf : ∀ n, (f n).Monic) : (limit f hf).map (Ideal.Quotient.mk (I ^ n)) = f n := by
  obtain hi | hi := eq_or_ne I ⊤
  · subst hi; subsingleton [IsAdicComplete.subsingleton R ‹_›]
  obtain _ | n := n
  · subsingleton [Ideal.Quotient.subsingleton_iff.mpr (show I ^ 0 = ⊤ by simp)]
  have h₁ (n) : I ^ (n + 1) ≠ ⊤ := by simpa [pow_eq_top_iff]
  have h₂ (n) := Ideal.Quotient.nontrivial_iff.2 (h₁ n)
  have hn : (f (n + 1)).natDegree = (f 1).natDegree := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, eq_comm, ← hf]; exact (mf (n + 2)).natDegree_map _
  ext i
  rw [coeff_map, limit, coeff_sum_C_mul_X_pow]
  split_ifs with hin
  · rw [mk_ofLinearEquiv_symm_mkRing]
  · rw [map_zero, coeff_eq_zero_of_natDegree_lt (hn ▸ by grind)]

/-- Degree of a polynomial explicitly given as `∑ i, C (f i) * X ^ i`. -/
theorem _root_.Polynomial.degree_sum_lt' {R : Type*} [Semiring R] {n : ℕ} {f : ℕ → R} :
    (∑ i ∈ Finset.range n, C (f i) * X ^ i).degree < ↑n := by
  rw [Finset.sum_range]
  exact degree_sum_fin_lt _

/-- Degree of a polynomial explicitly given as `∑ i, C (f i) * X ^ i`. -/
theorem _root_.Polynomial.natDegree_sum_lt {R : Type*} [Semiring R] {n : ℕ} {f : ℕ → R}
    (hn : n ≠ 0) : (∑ i ∈ Finset.range n, C (f i) * X ^ i).natDegree < n := by
  by_cases h : ∑ i ∈ Finset.range n, C (f i) * X ^ i = 0
  · rwa [h, natDegree_zero, Nat.pos_iff_ne_zero]
  exact (natDegree_lt_iff_degree_lt h).mpr degree_sum_lt'

theorem _root_.Polynomial.coeff_limit_natDegree {f : ∀ n, (R ⧸ I ^ n)[X]} {hf}
    (mf : ∀ n, (f n).Monic) : (limit f hf).coeff (f 1).natDegree = 1 := by
  refine (IsHausdorff.eq_iff_eq (I := I)).mpr fun n ↦ ?_
  rw [limit, coeff_sum_C_mul_X_pow, if_pos (by grind), mk_ofLinearEquiv_symm_mkRing]
  obtain hi | hi := eq_or_ne I ⊤
  · subst hi
    have := IsAdicComplete.subsingleton R ‹_›
    subsingleton
  have h₁ (n) : I ^ (n + 1) ≠ ⊤ := by simpa [pow_eq_top_iff]
  have h₂ (n) := Ideal.Quotient.nontrivial_iff.2 (h₁ n)
  have h₃ (n) : (f (n + 1)).natDegree = (f 1).natDegree := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, eq_comm, ← hf]; exact (mf (n + 2)).natDegree_map _
  obtain _ | n := n
  · subsingleton [Ideal.Quotient.subsingleton_iff.mpr (show I ^ 0 = ⊤ by simp)]
  rw [← h₃ n, map_one]
  exact mf _

theorem _root_.Polynomial.natDegree_limit {f : ∀ n, (R ⧸ I ^ n)[X]} {hf} (mf : ∀ n, (f n).Monic) :
    (limit f hf).natDegree = (f 1).natDegree := by
  obtain hi | hi := eq_or_ne I ⊤
  · subst hi
    have := IsAdicComplete.subsingleton R ‹_›
    simp [natDegree_of_subsingleton]
  have h₁ (n) : I ^ (n + 1) ≠ ⊤ := by simpa [pow_eq_top_iff]
  have h₂ (n) := Ideal.Quotient.nontrivial_iff.2 (h₁ n)
  nontriviality R
  exact natDegree_eq_of_le_of_coeff_ne_zero (Nat.le_of_lt_succ <| natDegree_sum_lt (by grind))
    (by rw [coeff_limit_natDegree mf]; exact one_ne_zero)

theorem _root_.Polynomial.monic_limit {f : ∀ n, (R ⧸ I ^ n)[X]} {hf} (mf : ∀ n, (f n).Monic) :
    (limit f hf).Monic := by
  rw [Monic, leadingCoeff, natDegree_limit mf, coeff_limit_natDegree mf]

instance : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)

/-- A monic coprime factorisation of `f` in `(R ⧸ I)[X]` lifts to a monic factorisation of `f` in
`R[X]`. (Does it have to be coprime as well?) -/
noncomputable def liftAdic {f : R[X]} (mf : f.Monic)
    (fac : MonicCoprimeFactors (f.map (Ideal.Quotient.mk I))) :
    MonicFactors f where
  fst := limit (I := I) (fun n ↦ n.casesOn 1 fun n ↦ ((liftFactorPow I mf).symm fac).fst) fun n ↦
    n.casesOn (Subsingleton.elim _ _) fun n ↦ by rw [← map_fst, fst_map_factorPowSucc_liftFactorPow]
  snd := limit (I := I) (fun n ↦ n.casesOn 1 fun n ↦ ((liftFactorPow I mf).symm fac).snd) fun n ↦
    n.casesOn (Subsingleton.elim _ _) fun n ↦ by rw [← map_snd, snd_map_factorPowSucc_liftFactorPow]
  monic_fst := monic_limit fun n ↦ n.casesOn monic_one fun _ ↦ monic_fst _
  monic_snd := monic_limit fun n ↦ n.casesOn monic_one fun _ ↦ monic_snd _
  fst_mul_snd_eq := by
    ext i
    refine (IsHausdorff.eq_iff_eq (I := I)).mpr fun n ↦ ?_
    rw [← coeff_map, ← coeff_map, Polynomial.map_mul,
      map_limit (fun n ↦ n.casesOn monic_one fun _ ↦ monic_fst _),
      map_limit (fun n ↦ n.casesOn monic_one fun _ ↦ monic_snd _)]
    obtain _ | n := n
    · subsingleton
    simp only [fst_mul_snd_eq]

@[simp] theorem map_fst_liftAdic {fac} :
    (liftAdic (I := I) mf fac).fst.map (Ideal.Quotient.mk I) = fac.fst := by
  conv => enter [1,1]; exact (factor_comp_mk (show I ^ 1 ≤ I by simp)).symm
  rw [← Polynomial.map_map, liftAdic, map_limit fun n ↦ n.casesOn monic_one fun _ ↦ monic_fst _,
    Nat.casesOn, Nat.rec_one, ← map_fst, ← liftFactorPow_fst I (mf := mf), Equiv.apply_symm_apply]

@[simp] theorem map_snd_liftAdic {fac} :
    (liftAdic (I := I) mf fac).snd.map (Ideal.Quotient.mk I) = fac.snd := by
  conv => enter [1,1]; exact (factor_comp_mk (show I ^ 1 ≤ I by simp)).symm
  rw [← Polynomial.map_map, liftAdic, map_limit fun n ↦ n.casesOn monic_one fun _ ↦ monic_snd _,
    Nat.casesOn, Nat.rec_one, ← map_snd, ← liftFactorPow_snd I (mf := mf), Equiv.apply_symm_apply]

theorem map_comp_liftAdic : MonicFactors.map (Ideal.Quotient.mk I) ∘ liftAdic (I := I) mf =
    toMonicFactors := by
  ext : 2 <;> simp

theorem liftAdic_injective : (liftAdic (I := I) mf).Injective :=
  .of_comp <| by rw [map_comp_liftAdic]; exact toMonicFactors_injective

end MonicCoprimeFactors

open MonicFactors

/-- If `f ≠ 1` then we have at least `f = f * 1` and `f = 1 * f`. -/
theorem two_le_card_monicFactors [Semiring R] {f : R[X]} (mf : f.Monic) (hf1 : f ≠ 1)
    [Finite f.MonicFactors] : 2 ≤ Nat.card f.MonicFactors :=
  Nat.card_fin 2 ▸ Nat.card_le_card_of_injective ![fstOne mf, sndOne mf] <| by
    rwa [injective_pair_iff_ne, ne_eq, fstOne_eq_sndOne_iff]

/-- If `f ≠ 1` then we have at least `f = f * 1` and `f = 1 * f`. -/
theorem two_le_card_monicCoprimeFactors [CommSemiring R] {f : R[X]} (mf : f.Monic) (hf1 : f ≠ 1)
    [Finite f.MonicCoprimeFactors] : 2 ≤ Nat.card f.MonicCoprimeFactors :=
  Nat.card_fin 2 ▸ Nat.card_le_card_of_injective
    ![MonicCoprimeFactors.fstOne mf, .sndOne mf] <| by
    rwa [injective_pair_iff_ne, ne_eq, MonicCoprimeFactors.fstOne_eq_sndOne_iff]

/-- If a monic polynomial `f` is irreducible, then only monic factorisations are `1 * f` and
`f * 1`. -/
theorem forall_monicFactors_of_irreducible [Semiring R] {f : R[X]}
    (mf : f.Monic) (hf : Irreducible f) (fac : MonicFactors f) :
    fac = fstOne mf ∨ fac = sndOne mf := by
  obtain ⟨p, q, mp, mq, eq⟩ := fac
  refine (of_irreducible_mul <| eq ▸ hf).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · rw [mp.isUnit_iff] at h; subst p
    rw [one_mul] at eq; subst q
    rfl
  · rw [mq.isUnit_iff] at h; subst q
    rw [mul_one] at eq; subst p
    rfl

/-- If the only monic factorisations are `1 * f` and `f * 1`, then `f` is irreducible.

We need domain, because in `ZMod 6` we have `X = (2X+3)(3X+2)`. -/
theorem irreducible_of_forall_monicFactors [CommSemiring R] [NoZeroDivisors R]
    {f : R[X]} (mf : f.Monic) (hf1 : f ≠ 1)
    (hf : ∀ fac : MonicFactors f, fac = fstOne mf ∨ fac = sndOne mf) :
    Irreducible f := by
  refine ⟨mt mf.isUnit_iff.mp hf1, fun a b hab ↦ ?_⟩
  rw [hab, Monic, leadingCoeff_mul] at mf
  have ha : IsUnit a.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨_, mf⟩
  have hb : IsUnit b.leadingCoeff := isUnit_iff_exists_inv'.mpr ⟨_, mf⟩
  specialize hf ⟨_, _, monic_of_isUnit_leadingCoeff_inv_smul ha,
    monic_of_isUnit_leadingCoeff_inv_smul hb, _⟩
  · rw [← smul_eq_mul, smul_assoc, smul_comm a, ← mul_smul, ← mul_inv, inv_smul_eq_iff, smul_eq_mul,
      ← hab, ← IsUnit.unit_mul, Units.smul_isUnit, mf, one_smul]
  refine hf.imp (fun h ↦ ?_) (fun h ↦ ?_)
  · rw [← isUnit_smul_iff (ha.unit⁻¹) a, show _ • _ = (1 : R[X]) from congr(($h).fst)]
    exact isUnit_one
  · rw [← isUnit_smul_iff (hb.unit⁻¹) b, show _ • _ = (1 : R[X]) from congr(($h).snd)]
    exact isUnit_one

theorem forall_monicFactors_of_natDegree_le_one [Semiring R] {f : R[X]}
    (hdf : f.natDegree ≤ 1) (mf : f.Monic) (fac : MonicFactors f) :
    fac = fstOne mf ∨ fac = sndOne mf := by
  obtain ⟨p, q, mp, mq, eq⟩ := fac
  have h₁ := mp.natDegree_mul mq
  obtain hdf | hdf := Nat.le_one_iff_eq_zero_or_eq_one.mp hdf
  · rw [eq, hdf, eq_comm, Nat.add_eq_zero_iff, mp.natDegree_eq_zero, mq.natDegree_eq_zero] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    rw [mul_one] at eq; subst eq
    exact .inl rfl
  · rw [eq, hdf, eq_comm, Nat.add_eq_one_iff, mp.natDegree_eq_zero, mq.natDegree_eq_zero] at h₁
    obtain ⟨rfl, -⟩ | ⟨-, rfl⟩ := h₁
    · rw [one_mul] at eq; subst q
      exact .inl rfl
    · rw [mul_one] at eq; subst p
      exact .inr rfl

noncomputable instance [Semiring R] : Unique (MonicFactors (1 : R[X])) where
  default := fstOne monic_one
  uniq fac := by
    obtain rfl | rfl := forall_monicFactors_of_natDegree_le_one (f := (1 : R[X])) (by simp)
      (by simp) fac <;> rfl

noncomputable instance [CommSemiring R] : Unique (MonicCoprimeFactors (1 : R[X])) where
  default := .fstOne monic_one
  uniq fac := by
    obtain h | h := forall_monicFactors_of_natDegree_le_one (f := (1 : R[X])) (by simp)
      (by simp) fac.toMonicFactors <;> exact MonicCoprimeFactors.toMonicFactors_injective h

/-- A monic polynomial `f` is irreducible iff `#(MonicFactors f) = 2`.

We need domain because of the counter-example in `ZMod 6` where `X = (2X+3)(3X+2)`. -/
theorem irreducible_iff_card_monicFactors [CommSemiring R] [NoZeroDivisors R]
    {f : R[X]} (mf : f.Monic) :
    Irreducible f ↔ Nat.card (MonicFactors f) = 2 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rw [← Nat.card_fin 2, eq_comm]
    refine Nat.card_eq_of_bijective ![fstOne mf, sndOne mf] ⟨?_, fun fac ↦ ?_⟩
    · rw [injective_pair_iff_ne, ne_eq, fstOne_eq_sndOne_iff]
      exact hf.ne_one
    · obtain rfl | rfl := forall_monicFactors_of_irreducible mf hf fac
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  · have hf1 : f ≠ 1 := by
      rintro rfl
      simp at hf
    refine irreducible_of_forall_monicFactors mf hf1 fun fac ↦ ?_
    have := (Nat.card_pos_iff.mp (hf ▸ show 0 < 2 by decide)).2
    obtain ⟨a, rfl⟩ := (Function.Injective.bijective_of_nat_card_le (f := ![fstOne mf, sndOne mf])
      (by rwa [injective_pair_iff_ne, ne_eq, fstOne_eq_sndOne_iff])
      (by rw [Nat.card_fin]; exact hf.le)).2 fac
    obtain rfl | rfl := or_iff_not_imp_left.mpr a.eq_one_of_ne_zero
    · exact .inl rfl
    · exact .inr rfl

/-- Over a domain, a **separable** monic polynomial is irreducible iff
`#(MonicCoprimeFactors f) = 2`. -/
theorem irreducible_iff_card_monicCoprimeFactors [CommSemiring R] [NoZeroDivisors R]
    {f : R[X]} (mf : f.Monic) (sf : f.Separable) :
    Irreducible f ↔ Nat.card (MonicCoprimeFactors f) = 2 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rw [← Nat.card_fin 2, eq_comm]
    refine Nat.card_eq_of_bijective ![.fstOne mf, .sndOne mf] ⟨?_, fun fac ↦ ?_⟩
    · rw [injective_pair_iff_ne, ne_eq, MonicCoprimeFactors.fstOne_eq_sndOne_iff]
      exact hf.ne_one
    · obtain hfac | hfac := forall_monicFactors_of_irreducible mf hf fac.toMonicFactors
      · exact ⟨0, MonicCoprimeFactors.toMonicFactors_injective hfac.symm⟩
      · exact ⟨1, MonicCoprimeFactors.toMonicFactors_injective hfac.symm⟩
  · have hf1 : f ≠ 1 := by
      rintro rfl
      simp at hf
    refine irreducible_of_forall_monicFactors mf hf1 fun fac ↦ ?_
    have := (Nat.card_pos_iff.mp (hf ▸ show 0 < 2 by decide)).2
    obtain ⟨a, ha⟩ := (Function.Injective.bijective_of_nat_card_le
      (f := ![MonicCoprimeFactors.fstOne mf, .sndOne mf])
      (by rwa [injective_pair_iff_ne, ne_eq, MonicCoprimeFactors.fstOne_eq_sndOne_iff])
      (by rw [Nat.card_fin]; exact hf.le)).2
      { fac with coprime_fst_snd := Polynomial.Separable.isCoprime <| by rwa [fac.5] }
    obtain rfl | rfl := or_iff_not_imp_left.mpr a.eq_one_of_ne_zero
    · exact .inl congr(($ha.symm).toMonicFactors)
    · exact .inr congr(($ha.symm).toMonicFactors)

/-- **Hensel's lemma**: If `R` is `I`-adically complete, and both `R` and `R ⧸ I` are domains,
then any irreducible monic polynomial in `R` that is separable in `R ⧸ I` is also irreducible
in `R ⧸ I`. -/
theorem irreducible_map_of_irreducible_of_separable_map [CommRing R] [NoZeroDivisors R]
    {I : Ideal R} [I.IsPrime] [IsAdicComplete I R] {f : R[X]}
    (monic : f.Monic) (irr : Irreducible f) (sep_map : (f.map (Ideal.Quotient.mk I)).Separable) :
    Irreducible (f.map (Ideal.Quotient.mk I)) := by
  have hf1 : f.map (Ideal.Quotient.mk I) ≠ 1 := fun hf1 ↦ by
    rw [← (monic.map _).natDegree_eq_zero, monic.natDegree_map, monic.natDegree_eq_zero] at hf1
    subst hf1
    simp at irr
  rw [irreducible_iff_card_monicFactors monic] at irr
  have := (Nat.card_pos_iff.mp (irr ▸ show 0 < 2 by decide)).2
  have := this.of_injective _ (MonicCoprimeFactors.liftAdic_injective (I := I) (mf := monic))
  rw [irreducible_iff_card_monicCoprimeFactors (monic.map _) sep_map]
  refine le_antisymm ?_ (two_le_card_monicCoprimeFactors (monic.map _) hf1)
  rw [← irr]
  exact Nat.card_le_card_of_injective _ (MonicCoprimeFactors.liftAdic_injective (mf := monic))

end Polynomial
