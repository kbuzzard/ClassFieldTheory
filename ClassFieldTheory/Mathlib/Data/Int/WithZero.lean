module

public import Mathlib.Data.Int.WithZero

public section

open NNReal

@[simp] lemma WithZeroMulInt.toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) {n : ℤ} :
    WithZeroMulInt.toNNReal he (.exp n) = e ^ n := by rfl
