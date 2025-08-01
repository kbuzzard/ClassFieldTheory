import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

open CategoryTheory Limits

namespace groupCohomology
universe u
variable {R G : Type u} [CommRing R] [Group G] {A : Rep R G}

/--
If `M` is a trivial representation of a finite group `G` and `M` is torsion-free
then `H¹(G,M) = 0`.
-/
lemma H1_isZero_of_trivial (M : Rep R G) [NoZeroSMulDivisors ℕ M] [M.IsTrivial] [Finite G] :
    IsZero (H1 M) := by
  /-
  Since `M` is a trivial representation, we can identify `H¹(G,M)` with `Hom(G,M)`,
  which is zero if `G` is finite and `M` is torsion-free.

  This uses `groupCohomology.H1LequivOfIsTrivial`.
  -/
  refine .of_iso ?_ (groupCohomology.H1IsoOfIsTrivial M)
  have (f : (ModuleCat.of R (Additive G →+ ↑M.V))) : f = 0 := by
    ext g
    have : IsOfFinAddOrder (Additive.ofMul g) := isOfFinAddOrder_of_finite _
    obtain ⟨n, hpos, hn⟩ := this.exists_nsmul_eq_zero
    have : n • f (Additive.ofMul g) = 0 := by simp [← AddMonoidHom.map_nsmul, hn]
    aesop
  have : Subsingleton (ModuleCat.of R (Additive G →+ ↑M.V)) := subsingleton_of_forall_eq 0 this
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Additive G →+ ↑M.V))

namespace cocycles₂

@[simp, norm_cast] lemma coe_zero : ⇑(0 : cocycles₂ A) = 0 := rfl
@[simp, norm_cast] lemma coe_add (a b : cocycles₂ A) : ⇑(a + b) = a + b := rfl

-- TODO: Replace `coe_mk` in mathlib
@[simp, norm_cast] lemma coe_mk' (f : G × G → A) (hf) : ⇑(⟨f, hf⟩ : cocycles₂ A) = f := rfl

end cocycles₂

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_H2Iso_hom :
    H2π A ≫ (H2Iso A).hom = (shortComplexH2 A).moduleCatLeftHomologyData.π := by simp [H2π]

end groupCohomology
