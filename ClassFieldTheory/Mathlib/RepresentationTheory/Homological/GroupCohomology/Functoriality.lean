module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep

universe u
variable {R G : Type u} [CommRing R] [Group G] {M : Rep R G}

namespace groupCohomology

@[simp]
lemma res_id : res (MonoidHom.id G) M = M := rfl

end groupCohomology
