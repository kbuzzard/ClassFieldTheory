import Mathlib.GroupTheory.Torsion

variable {M N : Type*} [Monoid M] [Monoid N]

variable (M N) in
-- TODO: Make `Monoid.IsTorsion` a typeclass
@[to_additive]
lemma subsingleton_monoidHom_of_isTorsion_isMulTorsionFree (hM : Monoid.IsTorsion M)
    [IsMulTorsionFree N] : Subsingleton (M →* N) where
  allEq f g := by
    ext m
    obtain ⟨n, hn, hrm⟩ := isOfFinOrder_iff_pow_eq_one.1 <| hM m
    refine pow_left_injective hn.ne' ?_
    simp_all [← map_pow]
