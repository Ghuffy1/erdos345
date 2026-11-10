import Erdos345.LevParameterBounds

namespace Erdos345

theorem sharp_interval_ratio (m : ℕ) (hm : 1536 ≤ m) :
    3 ≤ m / 16 ∧ 2 * m ≤ 33 * (m / 16 - 2) + 1 := by
  have hq : 96 ≤ m / 16 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmod := Nat.mod_lt m (show 0 < 16 by omega)
  have heq := Nat.mod_add_div m 16
  omega

end Erdos345
