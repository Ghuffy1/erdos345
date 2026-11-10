import Erdos345.SmallHeightTriviality

namespace Erdos345

theorem energyHeightConstant_mono (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (E : ℝ) :
    energyHeightConstant N E ≤ energyHeightConstant M E := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := hNR.trans_le (by exact_mod_cast hNM)
  have hfrac : Real.pi / (64 * (M : ℝ)) ≤ Real.pi / (64 * (N : ℝ)) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hNM) (by norm_num))
  have hlog := Real.log_le_log (by positivity : 0 < Real.pi / (64 * (M : ℝ))) hfrac
  unfold energyHeightConstant
  exact max_le_max le_rfl (by linarith)

theorem conductorCoefficient_mono (N M k : ℕ) (hNM : N ≤ M) :
    conductorCoefficient N k ≤ conductorCoefficient M k := by
  have hlog : (Nat.log 2 N : ℝ) ≤ Nat.log 2 M := by exact_mod_cast Nat.log_mono_right hNM
  unfold conductorCoefficient
  gcongr

/-- A proper-degree envelope and a separate initial bound suffice for all
degrees used in the least-degree argument, including the initial degree k. -/
theorem log_bound_for_all_reductions (q k : ℕ) (hq : 0 < q) (H : ℝ)
    (hinitial : Real.log (q : ℝ) ≤ H * k)
    (hproper : ∀ d : ℕ, 0 < d → d < k → Real.log (reductionModulus k d : ℝ) ≤ H * d) :
    ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d → Real.log (q : ℝ) ≤ H * d := by
  intro d hd hdk hred
  by_cases h : d = k
  · simpa only [h] using hinitial
  · have hdlt : d < k := lt_of_le_of_ne hdk h
    have hqg : q ≤ reductionModulus k d := Nat.le_of_dvd (reductionModulus_pos hdlt) hred
    exact (Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqg)).trans (hproper d hd hdlt)

end Erdos345
