import Mathlib.Algebra.Group.Action.Units

def Units.mulDistribMulActionRight (G M : Type*) [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    MulDistribMulAction G Mˣ where
  smul g u := ⟨g • u, g • u⁻¹, by simp [← smul_mul', smul_one], by simp [← smul_mul', smul_one]⟩
  one_smul u := Units.ext <| one_smul ..
  mul_smul g₁ g₂ u := Units.ext <| mul_smul ..
  smul_mul g₁ u₁ u₂ := Units.ext <| smul_mul' ..
  smul_one g := Units.ext <| smul_one g

attribute [local instance] Units.mulDistribMulActionRight

@[simp] lemma Units.coe_smul {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M]
    {g : G} {u : Mˣ} : (g • u : Mˣ).val = g • u.val := rfl
