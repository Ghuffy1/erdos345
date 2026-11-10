import Erdos345.ReducedPhaseRecurrence

namespace Erdos345

theorem windowHeightBudget_antitone_length (N J q W L : ℕ) (hN : 1 ≤ N)
    (hq : 0 < q) (hW : (16 : ℝ) ≤ W) (hWL : W ≤ L) (E : ℝ) :
    windowHeightBudget N J q L E ≤ windowHeightBudget N J q W E := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hC : 0 ≤ energyHeightConstant N E := le_max_left _ _
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by linarith)
  have hlogWL : Real.log (W : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hWL)
  unfold windowHeightBudget
  apply max_le_max le_rfl
  apply max_le_max
  · exact div_le_div_of_nonneg_left (by positivity) hlogW hlogWL
  · exact div_le_div_of_nonneg_left (by positivity) hlogW hlogWL

theorem windowHeightBudget_le_explicit (N J q L : ℕ) (hN : 1 ≤ N)
    (hq : 0 < q) (hL : (16 : ℝ) ≤ L) (E : ℝ) :
    windowHeightBudget N J q L E ≤
      (2 * Real.log q + (N : ℝ) * energyHeightConstant N E +
        8 * (J : ℝ) * Real.log N) / Real.log L := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hC : 0 ≤ energyHeightConstant N E := le_max_left _ _
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNC : energyHeightConstant N E ≤ (N : ℝ) * energyHeightConstant N E := by
    nlinarith
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have hterm : 0 ≤ (J : ℝ) * Real.log N := mul_nonneg (Nat.cast_nonneg _) hlogN
  unfold windowHeightBudget
  apply max_le
  · apply div_nonneg
    · positivity
    · exact hlogL.le
  · apply max_le
    · exact div_le_div_of_nonneg_right (by linarith) hlogL.le
    · exact div_le_div_of_nonneg_right (by linarith) hlogL.le

theorem windowHeightBudget_le_log_envelope (N J q L : ℕ) (hN : 1 ≤ N)
    (hq : 0 < q) (hL : (16 : ℝ) ≤ L) (hJN : J ≤ N) (E R K : ℝ)
    (hC : energyHeightConstant N E ≤ R) (hK : Real.log (N : ℝ) ≤ K) :
    windowHeightBudget N J q L E ≤
      (2 * Real.log q + (N : ℝ) * (R + 8 * K)) / Real.log L := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hC0 : 0 ≤ energyHeightConstant N E := le_max_left _ _
  have hK0 : 0 ≤ K := hlogN.trans hK
  have hJN' : (J : ℝ) ≤ N := by exact_mod_cast hJN
  have hprod : (J : ℝ) * Real.log N ≤ (N : ℝ) * K :=
    mul_le_mul hJN' hK hlogN (Nat.cast_nonneg _)
  have hNC : (N : ℝ) * energyHeightConstant N E ≤ (N : ℝ) * R :=
    mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
  refine (windowHeightBudget_le_explicit N J q L hN hq hL E).trans ?_
  apply div_le_div_of_nonneg_right
  · nlinarith
  · exact (Real.log_pos (by linarith : (1 : ℝ) < L)).le

theorem windowHeightBudget_le_linear_degree (d J q L : ℕ) (hd : 0 < d)
    (hq : 0 < q) (hL : (16 : ℝ) ≤ L) (hJ : J ≤ d + 1) (E R K H : ℝ)
    (hC : energyHeightConstant (d + 1) E ≤ R)
    (hK : Real.log ((d + 1 : ℕ) : ℝ) ≤ K)
    (hlogq : Real.log (q : ℝ) ≤ H * d) :
    windowHeightBudget (d + 1) J q L E ≤
      ((2 * H + 2 * R + 16 * K) / Real.log L) * d := by
  have hC0 : 0 ≤ energyHeightConstant (d + 1) E := le_max_left _ _
  have hR0 : 0 ≤ R := hC0.trans hC
  have hK0 : 0 ≤ K := (Real.log_nonneg (by exact_mod_cast (show 1 ≤ d + 1 by omega))).trans hK
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hprod : ((d + 1 : ℕ) : ℝ) * (R + 8 * K) ≤ (2 * d : ℝ) * (R + 8 * K) := by
    push_cast
    nlinarith
  refine (windowHeightBudget_le_log_envelope (d + 1) J q L (by omega) hq hL hJ E R K hC hK).trans ?_
  calc
    _ ≤ ((2 * H + 2 * R + 16 * K) * d) / Real.log L := by
      apply div_le_div_of_nonneg_right
      · nlinarith
      · exact (Real.log_pos (by linarith : (1 : ℝ) < L)).le
    _ = _ := by ring

end Erdos345
