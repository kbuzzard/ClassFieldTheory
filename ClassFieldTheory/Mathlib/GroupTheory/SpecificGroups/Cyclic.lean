import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace IsCyclic
variable {G : Type*} [Group G] [instCyclic : IsCyclic G]

variable (G) in
/-- `gen G` is a generator of the cyclic group `G`. -/
noncomputable def gen : G := IsCyclic.exists_generator.choose

lemma gen_generate (x : G) : x ∈ Subgroup.zpowers (gen G) := exists_generator.choose_spec x

theorem unique_gen_zpow_zmod [Fintype G] (x : G) :
    ∃! n : ZMod (Fintype.card G), x = gen G ^ n.val :=
  IsCyclic.unique_zpow_zmod gen_generate x

theorem unique_gen_pow [Fintype G] (x : G) : ∃! n < Fintype.card G, x = gen G ^ n := by
  obtain ⟨k, hk, hk_unique⟩ := unique_gen_zpow_zmod x
  refine ⟨k.val, ⟨⟨ZMod.val_lt _, hk⟩, ?_⟩⟩
  intro y ⟨hy_lt, hy⟩
  rw [← hk_unique y]
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy_lt]
  · simp [hy]

end IsCyclic
