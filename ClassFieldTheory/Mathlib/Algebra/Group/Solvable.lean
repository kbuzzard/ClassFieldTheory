import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Solvable

@[simp, norm_cast]
theorem Pi.coe_evalMonoidHom.{u, v} {I : Type u} (f : I → Type v) [(i : I) → MulOneClass (f i)] (i : I) :
    ⇑(Pi.evalMonoidHom f i) = Function.eval i := rfl

theorem Subgroup.Quotient.nontrivial_of_ne_top {G : Type*} [Group G] {p : Subgroup G} (h : p ≠ ⊤) :
    Nontrivial (G ⧸ p) := by
  obtain ⟨x, -, notMem_s⟩ : ∃ x ∈ ⊤, x ∉ p := SetLike.exists_of_lt (lt_top_iff_ne_top.2 h)
  refine ⟨⟨QuotientGroup.mk x, QuotientGroup.mk 1, ?_⟩⟩
  simpa [QuotientGroup.eq] using notMem_s

theorem CommGroup.exists_mulHom_zmod_surjective_of_finite (G : Type*) [CommGroup G] [Finite G] [Nontrivial G] :
    ∃ n > 1, ∃ (f : G →* Multiplicative (ZMod n)), (⇑f).Surjective := by
  obtain ⟨ι, _, n, hn1, ⟨equiv⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨i⟩ : Nonempty ι := by
    rw [← not_isEmpty_iff]
    intro
    apply not_subsingleton G
    exact equiv.subsingleton
  refine ⟨n i, hn1 i, (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp equiv, ?_⟩
  simp [Function.surjective_eval]

theorem exists_isCyclic_quotient_of_finite {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    (hH: H ≠ ⊤) (comm : IsMulCommutative (G ⧸ H)) : ∃ H' ∈ Set.Ico H ⊤, ∃ (_ : H'.Normal), IsCyclic (G ⧸ H') := by
  have := Subgroup.Quotient.nontrivial_of_ne_top hH
  obtain ⟨n, hn, f, hf⟩ := CommGroup.exists_mulHom_zmod_surjective_of_finite (G ⧸ H)
  refine ⟨(f.comp (QuotientGroup.mk' H)).ker, ?_, inferInstance, ?_⟩
  · rw [Set.mem_Ico, ← MonoidHom.comap_ker, ← Subgroup.map_le_iff_le_comap,
      QuotientGroup.map_mk'_self, and_iff_right bot_le, lt_top_iff_ne_top,
      ← Subgroup.comap_top (QuotientGroup.mk' H), (Subgroup.comap_injective (QuotientGroup.mk'_surjective H)).ne_iff,
      ne_eq, MonoidHom.ker_eq_top_iff]
    rintro rfl
    apply Fact.mk at hn
    have := uniqueOfSurjectiveOne (G ⧸ H) hf
    exact not_subsingleton (ZMod n) Multiplicative.ofAdd.subsingleton
  · exact (QuotientGroup.quotientKerEquivRange _).isCyclic.2 inferInstance

theorem solvable_ind {G : Type*} [Group G] [IsSolvable G] [Finite G] {motive : Subgroup G → Prop}
    (bot : motive ⊥) (ind : ∀ (H H' : Subgroup G) (_ : H ≤ H') (normal : (H.subgroupOf H').Normal),
      IsCyclic (H' ⧸ H.subgroupOf H') → motive H → motive H') (t : Subgroup G) : motive t := by
  by_cases ht : t = ⊥
  · exact ht ▸ bot
  · have hhh : ⁅t, t⁆ < t := IsSolvable.commutator_lt_of_ne_bot ht
    have sub_eq : (⁅t, t⁆).subgroupOf t = commutator t := by
      apply Subgroup.map_injective t.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hhh.le, map_commutator_eq, Subgroup.range_subtype]
    have normal : ((⁅t, t⁆).subgroupOf t).Normal := by
      rw [sub_eq]
      infer_instance
    have comm : IsMulCommutative (t ⧸ (⁅t, t⁆).subgroupOf t) := by
      revert normal
      rw [sub_eq]
      intro normal
      simp_rw [← Abelianization.eq_def]
      exact ⟨⟨mul_comm⟩⟩
    have htt : (⁅t, t⁆).subgroupOf t ≠ ⊤ := by simpa using hhh.not_ge
    obtain ⟨t', ⟨-, ht'⟩, _, cyclic⟩ := exists_isCyclic_quotient_of_finite htt comm
    have h : (Subgroup.map t.subtype t').subgroupOf t = t' := by
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective t.subtype_injective]
    have normal : ((Subgroup.map t.subtype t').subgroupOf t).Normal :=
      (congrArg Subgroup.Normal h).mpr inferInstance
    apply ind (t'.map t.subtype) t ((Subgroup.map_mono ht'.le).trans_eq
      ((MonoidHom.range_eq_map t.subtype).symm.trans t.range_subtype)) normal
      ((QuotientGroup.quotientMulEquivOfEq h).isCyclic.2 cyclic)
    have : Subgroup.map t.subtype t' < t := by
      apply ((Subgroup.map_lt_map_iff_of_injective t.subtype_injective).2 ht').trans_eq
      rw [← MonoidHom.range_eq_map t.subtype, t.range_subtype]
    exact solvable_ind bot ind (Subgroup.map t.subtype t')
termination_by wellFounded_lt.wrap t
