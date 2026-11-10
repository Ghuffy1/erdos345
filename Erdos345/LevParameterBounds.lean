import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Erdos345.TailCompletion

namespace Erdos345

/-- The integer ceiling used for Lev's multiplicity requirement, with
the nonzero-denominator condition supplied separately. -/
def levMultiplicityCeil (l n : ℕ) : ℕ := (l - 1 + (n - 2) - 1) / (n - 2)

theorem lev_parameters_large (m : ℕ) (hm : 128 ≤ m) :
    3 ≤ m / 16 ∧ levMultiplicityCeil (2 * m) (m / 16) ≤ 48 ∧
      2 * levMultiplicityCeil (2 * m) (m / 16) < 128 := by
  have hq : 8 ≤ m / 16 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmod := Nat.mod_lt m (show 0 < 16 by omega)
  have heq := Nat.mod_add_div m 16
  have hden : 0 < m / 16 - 2 := by omega
  have hnum : 2 * m - 1 + (m / 16 - 2) - 1 < 49 * (m / 16 - 2) := by omega
  have hbound : levMultiplicityCeil (2 * m) (m / 16) < 49 := by
    unfold levMultiplicityCeil
    exact (Nat.div_lt_iff_lt_mul hden).mpr hnum
  omega

theorem lev_interval_covers_next_power (N k s : ℕ) (hk : 0 < k)
    (hN : 128 ≤ N) (hkN : 2 * k ≤ N) (hs : 4 ≤ s) :
    (N + 1) ^ k ≤ 128 * (s * N ^ k / 16 - 1) := by
  have hp : N ≤ N ^ k := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (show 1 ≤ N by omega) (show 1 ≤ k by omega))
  have hpower : 128 ≤ N ^ k := hN.trans hp
  have hmul : 4 * N ^ k ≤ s * N ^ k := Nat.mul_le_mul_right (N ^ k) hs
  have hmod := Nat.mod_lt (s * N ^ k) (show 0 < 16 by omega)
  have heq := Nat.mod_add_div (s * N ^ k) 16
  have hlarge : 2 * N ^ k ≤ 128 * (s * N ^ k / 16 - 1) := by omega
  exact (next_power_le_twice (by omega) hkN).trans hlarge

end Erdos345
