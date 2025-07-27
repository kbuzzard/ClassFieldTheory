import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-- `L` with the spectral norm is a `NontriviallyNormedField`. -/
noncomputable
def spectralNorm.nontriviallyNormedField (K L : Type*) [NontriviallyNormedField K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsUltrametricDist K] [CompleteSpace K] :
    NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq <| (spectralNorm_extends _).symm⟩
