import Mathlib.RepresentationTheory.Basic

noncomputable section

namespace Representation
variable {k G V : Type*} [CommSemiring k] [Group G] [Finite G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- Given a representation `(V, ρ)` of a finite group `G`, `norm ρ` is the linear map `V →ₗ[k] V`
defined by `x ↦ ∑ ρ g x` for `g` in `G`. -/
def norm : Module.End k V :=
  have : Fintype G := .ofFinite _
  ∑ g : G, ρ g

@[simp]
lemma norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = norm ρ := by
  let : Fintype G := .ofFinite _
  ext
  simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ <| by simp

@[simp]
lemma norm_self_apply (g : G) (x : V) : norm ρ (ρ g x) = norm ρ x :=
  LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]
lemma self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = norm ρ := by
  let : Fintype G := .ofFinite _
  ext
  simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ <| by simp

@[simp]
lemma self_norm_apply (g : G) (x : V) : ρ g (norm ρ x) = norm ρ x :=
  LinearMap.ext_iff.1 (self_comp_norm _ _) x

end Representation
