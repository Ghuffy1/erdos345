import Erdos345.LogScaleGrowth

namespace Erdos345

open Filter

theorem degree_le_exp_logScale (k : ℕ) (hk : 0 < k) : (k : ℝ) ≤ Real.exp (logScale k) := by
  have he : 1 ≤ Real.exp (1 : ℝ) := (Real.one_le_exp_iff).mpr (by norm_num)
  have hm := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) k)
  rw [exp_logScale k hk]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem monomial_exp_logScale_bound (k a b : ℕ) (hk : 0 < k) (C D : ℝ) (hD : 0 ≤ D) :
    D * (k : ℝ) ^ a * logScale k ^ b * Real.exp (C * logScale k ^ 6) ≤
      Real.exp ((D + (a : ℝ) + b + C) * logScale k ^ 6) := by
  let K := logScale k
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK0 : 0 ≤ K := by linarith
  have hDexp : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hkexp : (k : ℝ) ^ a ≤ Real.exp K ^ a :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (degree_le_exp_logScale k hk) a
  have hKexp : K ^ b ≤ Real.exp K ^ b :=
    pow_le_pow_left₀ hK0 (by linarith [Real.add_one_le_exp K]) b
  have hm : D * (k : ℝ) ^ a * K ^ b * Real.exp (C * K ^ 6) ≤
      Real.exp D * Real.exp K ^ a * Real.exp K ^ b * Real.exp (C * K ^ 6) := by
    gcongr
  have heq : Real.exp D * Real.exp K ^ a * Real.exp K ^ b * Real.exp (C * K ^ 6) =
      Real.exp (D + (a : ℝ) * K + (b : ℝ) * K + C * K ^ 6) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hK16 : K ≤ K ^ 6 := by simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ 6 by decide)
  have hD6 := mul_le_mul_of_nonneg_left hK6 hD
  have ha6 := mul_le_mul_of_nonneg_left hK16 (Nat.cast_nonneg (α := ℝ) a)
  have hb6 := mul_le_mul_of_nonneg_left hK16 (Nat.cast_nonneg (α := ℝ) b)
  exact (hm.trans_eq heq).trans (Real.exp_le_exp.mpr (by dsimp only [K]; nlinarith))

/-- A fixed monomial in the degree and logarithmic scale, multiplied
by exp(C*K^6), is eventually dominated by exp(K^8/4). -/
theorem eventually_monomial_exp_dominated (a b : ℕ) (C D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop,
      D * (k : ℝ) ^ a * logScale k ^ b * Real.exp (C * logScale k ^ 6) ≤
        Real.exp (logScale k ^ 8 / 4) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_sixth_power_below_eighth (D + (a : ℝ) + b + C)] with k hk hbound
  exact (monomial_exp_logScale_bound k a b (by omega) C D hD).trans (Real.exp_le_exp.mpr hbound)

end Erdos345
