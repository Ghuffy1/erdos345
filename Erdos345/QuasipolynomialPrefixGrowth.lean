import Erdos345.CosineSourceInterface

namespace Erdos345

theorem centerPrefixPowerConstant_nonneg (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ centerPrefixPowerConstant C := by
  unfold centerPrefixPowerConstant
  have := centerPrefixLogConstant_nonneg
  linarith

theorem quasipolynomialCenterPrefix_pos (k : ℕ) (C : ℝ) :
    0 < quasipolynomialCenterPrefix k C := by
  have h : (0 : ℝ) < (quasipolynomialCenterPrefix k C : ℝ) :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem log_quasipolynomialCenterPrefix_le (k : ℕ) (hk : 0 < k) (C : ℝ) (hC : 0 ≤ C) :
    Real.log (quasipolynomialCenterPrefix k C : ℝ) ≤
      (centerPrefixPowerConstant C + 1) * logScale k ^ 6 := by
  let A := centerPrefixPowerConstant C * logScale k ^ 6
  have hA : 0 ≤ A := mul_nonneg (centerPrefixPowerConstant_nonneg C hC)
    (pow_nonneg (le_trans (by norm_num) (logScale_ge_one k hk)) _)
  have he : 1 ≤ Real.exp A := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos A).le
  change (quasipolynomialCenterPrefix k C : ℝ) < Real.exp A + 1 at hceil
  have hbound : (quasipolynomialCenterPrefix k C : ℝ) ≤ 2 * Real.exp A := by linarith
  have hpos : (0 : ℝ) < quasipolynomialCenterPrefix k C := by exact_mod_cast quasipolynomialCenterPrefix_pos k C
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hK6 : 1 ≤ logScale k ^ 6 := one_le_pow₀ (logScale_ge_one k hk)
  dsimp only [A] at hlog
  nlinarith

theorem quasipolynomialCenterPrefix_le_seventh_scale (k : ℕ) (hk : 0 < k)
    (C : ℝ) (hC : 0 ≤ C) (hK : centerPrefixPowerConstant C + 1 ≤ logScale k) :
    quasipolynomialCenterPrefix k C ≤ Nat.ceil (Real.exp (logScale k ^ 7)) := by
  have hlog := log_quasipolynomialCenterPrefix_le k hk C hC
  have hmul := mul_le_mul_of_nonneg_right hK (pow_nonneg (le_trans (by norm_num) (logScale_ge_one k hk)) 6)
  have hpower : logScale k * logScale k ^ 6 = logScale k ^ 7 := by ring
  rw [hpower] at hmul
  have hpos : (0 : ℝ) < quasipolynomialCenterPrefix k C := by exact_mod_cast quasipolynomialCenterPrefix_pos k C
  have h := (Real.log_le_iff_le_exp hpos).mp (hlog.trans hmul)
  have hceil := h.trans (Nat.le_ceil _)
  exact_mod_cast hceil

theorem eventually_logScale_ge (R : ℝ) : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → R ≤ logScale k := by
  refine ⟨Nat.ceil (Real.exp R) + 1, ?_⟩
  intro k hk
  have hkpos : 0 < k := by omega
  have hceil := Nat.le_ceil (Real.exp R)
  have hnat : Nat.ceil (Real.exp R) ≤ k := by omega
  have hcast : (Nat.ceil (Real.exp R) : ℝ) ≤ k := by exact_mod_cast hnat
  have hlog := Real.log_le_log (Real.exp_pos R) (hceil.trans hcast)
  rw [Real.log_exp] at hlog
  have hsecond := Real.log_le_log (show (0 : ℝ) < k by exact_mod_cast hkpos)
    (show (k : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k ≤ 2 * k by omega))
  unfold logScale
  linarith

theorem eventually_quasipolynomialCenterPrefix_le_seventh_scale (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      quasipolynomialCenterPrefix k C ≤ Nat.ceil (Real.exp (logScale k ^ 7)) := by
  obtain ⟨N, hN⟩ := eventually_logScale_ge (centerPrefixPowerConstant C + 1)
  refine ⟨max 1 N, ?_⟩
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left 1 N).trans hk)
  exact quasipolynomialCenterPrefix_le_seventh_scale k hkpos C hC
    (hN k ((le_max_right 1 N).trans hk))

end Erdos345
