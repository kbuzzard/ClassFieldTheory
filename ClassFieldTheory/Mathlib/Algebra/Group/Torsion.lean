import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Torsion

namespace Int

instance : IsAddTorsionFree ℤ where
  nsmul_right_injective n hn a b := Int.eq_of_mul_eq_mul_left (by simpa)

end Int
