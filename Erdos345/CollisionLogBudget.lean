import Erdos345.IntegerGridCollision

namespace Erdos345

theorem nat_mul_exp_le_exp (n : ℕ) (x y : ℝ) (h : Real.log (n : ℝ) + x ≤ y) :
    (n : ℝ) * Real.exp x ≤ Real.exp y := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, zero_mul]
    exact Real.exp_nonneg y
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      _ = Real.exp (Real.log (n : ℝ) + x) := by rw [Real.exp_add, Real.exp_log hnR]
      _ ≤ _ := Real.exp_le_exp.mpr h

/-- Explicit logarithmic budgets turn the two collision terms into a
single small upper bound. No eventual estimate is hidden here. -/
theorem powerCollisionSum_le_two_exp (R : Finset ℕ) (q k t L : ℕ)
    (Hhigh Hlow s : ℝ)
    (hbound : powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * Hhigh / R.card) +
      (L : ℝ) * Real.exp (-(t : ℝ) * Hlow / R.card))
    (hhigh : Real.log (q : ℝ) - (t : ℝ) * Hhigh / R.card ≤ -s)
    (hlow : Real.log (L : ℝ) - (t : ℝ) * Hlow / R.card ≤ -s) :
    powerCollisionSum R k q t ≤ 2 * Real.exp (-s) := by
  have hq := nat_mul_exp_le_exp q (-(t : ℝ) * Hhigh / R.card) (-s)
    (by simpa only [sub_eq_add_neg, neg_mul, neg_div] using hhigh)
  have hL := nat_mul_exp_le_exp L (-(t : ℝ) * Hlow / R.card) (-s)
    (by simpa only [sub_eq_add_neg, neg_mul, neg_div] using hlow)
  linarith

theorem two_exp_neg_lt_one (s : ℝ) (hs : Real.log 2 < s) : 2 * Real.exp (-s) < 1 := by
  have h : Real.exp (Real.log 2 - s) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show Real.log 2 - s < 0 by linarith)
  calc
    2 * Real.exp (-s) = Real.exp (Real.log 2 - s) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_neg, div_eq_mul_inv]
    _ < 1 := h

theorem powerCollisionSum_lt_one_of_log_budgets (R : Finset ℕ) (q k t L : ℕ)
    (Hhigh Hlow s : ℝ)
    (hbound : powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * Hhigh / R.card) +
      (L : ℝ) * Real.exp (-(t : ℝ) * Hlow / R.card))
    (hhigh : Real.log (q : ℝ) - (t : ℝ) * Hhigh / R.card ≤ -s)
    (hlow : Real.log (L : ℝ) - (t : ℝ) * Hlow / R.card ≤ -s)
    (hs : Real.log 2 < s) : powerCollisionSum R k q t < 1 :=
  (powerCollisionSum_le_two_exp R q k t L Hhigh Hlow s hbound hhigh hlow).trans_lt
    (two_exp_neg_lt_one s hs)

end Erdos345
