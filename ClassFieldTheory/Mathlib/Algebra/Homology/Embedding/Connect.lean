import Mathlib.Algebra.Homology.Embedding.Connect

open CategoryTheory Limits HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v, u} C] [HasZeroMorphisms C]
  {K : ChainComplex C ℕ} {L : CochainComplex C ℕ} (h : CochainComplex.ConnectData K L)
  {K' : ChainComplex C ℕ} {L' : CochainComplex C ℕ} (h' : CochainComplex.ConnectData K' L')
  {K'' : ChainComplex C ℕ} {L'' : CochainComplex C ℕ} (h'' : CochainComplex.ConnectData K'' L'')
  (fK : K ⟶ K') (fL : L ⟶ L') (f_comm : fK.f 0 ≫ h'.d₀ = h.d₀ ≫ fL.f 0)
  (fK' : K' ⟶ K'') (fL' : L' ⟶ L'') (f_comm' : fK'.f 0 ≫ h''.d₀ = h'.d₀ ≫ fL'.f 0)

namespace CochainComplex.ConnectData

@[simps]
protected def map : h.cochainComplex ⟶ h'.cochainComplex where
  f
    | Int.ofNat n => fL.f n
    | Int.negSucc n => fK.f n
  comm' i j := by
    rintro rfl
    obtain i | _ | i := i
    · exact fL.comm _ _
    · simpa
    · exact fK.comm _ _

@[simp]
lemma map_id : h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _ := by
  ext m; obtain m | _ | m := m <;> simp; rfl

lemma map_comp_map :
    h.map h' fK fL f_comm ≫ h'.map h'' fK' fL' f_comm' =
      h.map h'' (fK ≫ fK') (fL ≫ fL') (by simp [f_comm', reassoc_of% f_comm]) := by
  ext m; obtain m | _ | m := m <;> simp; rfl

lemma homologyMap_map_eq_pos (n : ℕ) (m : ℤ) (hmn : m = n + 1)
    [HasHomology h.cochainComplex m] [HasHomology L (n + 1)]
    [HasHomology h'.cochainComplex m] [HasHomology L' (n + 1)] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoPos n m hmn).hom ≫ homologyMap fL (n + 1) ≫ (h'.homologyIsoPos n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = ↑(n + 1) := hmn
  simp [ConnectData.map, -Int.natCast_add]

lemma homologyMap_map_eq_neg (n : ℕ) (m : ℤ) (hmn : m = -↑(n + 2))
    [HasHomology h.cochainComplex m] [HasHomology K (n + 1)]
    [HasHomology h'.cochainComplex m] [HasHomology K' (n + 1)] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoNeg n m hmn).hom ≫ homologyMap fK (n + 1) ≫ (h'.homologyIsoNeg n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = .negSucc (n + 1) := hmn
  simp [ConnectData.map, -Int.natCast_add]

end CochainComplex.ConnectData
