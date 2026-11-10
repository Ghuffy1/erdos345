import Erdos345.ShiftedPrimeProgressionCriterion
import Erdos345.PrimeSubsetGrowth
import Erdos345.ShiftedPrimeAsymptotics

namespace Erdos345

open Filter OAI.LargePrimeGaps
open scoped Topology

def shiftedPrimeCountingConstant : ℕ := 16 * 32768 * 32 ^ 8 * (2 ^ 24 * Nat.factorial 24)

theorem prime_subset_products_dominate (Y : ℕ) (hY : 16384 ≤ Y)
    (hbig : shiftedPrimeCountingConstant < Y) :
    4 * ((32768 * (32 * Y) ^ 8 : ℕ) : ℝ) * Real.log (primeProgressionScale Y : ℝ) <
      (primeSubsetProducts Y 24).card := by
  let D : ℝ := 2 ^ 24 * (Nat.factorial 24 : ℝ)
  let A : ℝ := 16 * 32768 * 32 ^ 8
  have hD : 0 < D := by dsimp [D]; positivity
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have hY0 : (0 : ℝ) < Y := by linarith
  have hbigR : A * D < (Y : ℝ) := by
    dsimp only [A, D]
    unfold shiftedPrimeCountingConstant at hbig
    exact_mod_cast hbig
  have h3 : A * D < (Y : ℝ) ^ 3 := hbigR.trans_le (le_self_pow₀ hY1 (by decide))
  have hp := mul_lt_mul_of_pos_right h3 (pow_pos hY0 9)
  have h12 : A * (Y : ℝ) ^ 9 < (Y : ℝ) ^ 12 / D := by
    apply (lt_div_iff₀ hD).mpr
    convert hp using 1 <;> ring
  have hlog := (log_prime_progression_scale_bounds Y (by omega)).2
  calc
    4 * ((32768 * (32 * Y) ^ 8 : ℕ) : ℝ) * Real.log (primeProgressionScale Y : ℝ) ≤
        4 * ((32768 * (32 * Y) ^ 8 : ℕ) : ℝ) * (4 * Y) := by gcongr
    _ = A * (Y : ℝ) ^ 9 := by dsimp [A]; push_cast; ring
    _ < (Y : ℝ) ^ 12 / D := h12
    _ ≤ (primeSubsetProducts Y 24).card := prime_subset_products_twenty_four_lower Y hY

theorem shifted_prime_requirement_below_scale (Y n : ℕ) (hY : 8 ≤ Y)
    (hn : Y ≤ n) (hupper : n ≤ primeProgressionScale Y * primeProgressionScale Y) :
    32768 * logScale (2 * (n + 1)) ^ 8 ≤ ((32768 * (32 * Y) ^ 8 : ℕ) : ℝ) := by
  have hY1 : 1 ≤ Y := by omega
  have hXpos : 0 < primeProgressionScale Y := by unfold primeProgressionScale; positivity
  have hXR : (0 : ℝ) < primeProgressionScale Y := by exact_mod_cast hXpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnu : (n : ℝ) ≤ (primeProgressionScale Y : ℝ) * primeProgressionScale Y := by
    exact_mod_cast hupper
  have hl := Real.log_le_log hnR hnu
  rw [Real.log_mul hXR.ne' hXR.ne'] at hl
  have hlogX := (log_prime_progression_scale_bounds Y hY1).2
  have hscale := doubled_logScale_le n (by omega)
  have htotal : logScale (2 * (n + 1)) ≤ 32 * Y := by linarith
  have hs0 : 0 ≤ logScale (2 * (n + 1)) :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans (logScale_ge_one _ (by omega))
  have hp := pow_le_pow_left₀ hs0 htotal 8
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 32768 by norm_num)
  exact_mod_cast hm

/-- The weak shifted-prime abundance sufficient for the original Erdős target follows
from Bombieri--Vinogradov. This statement keeps that input visible until it is proved. -/
theorem shifted_prime_abundance_of_bombieri_vinogradov (hbv : BombieriVinogradov) :
    ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ 2 ≤ n ∧
      32768 * logScale (2 * (n + 1)) ^ 8 ≤ (shiftedPrimes n).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_prime_progression_lower hbv)
  intro B
  let Y := max 16384 (max B (max N (shiftedPrimeCountingConstant + 1)))
  have hY : 16384 ≤ Y := le_max_left _ _
  have hYB : B ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYN : N ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbig : shiftedPrimeCountingConstant < Y := by dsimp [Y]; omega
  let X := primeProgressionScale Y
  let K := primorial Y
  let D := primeSubsetProducts Y 24
  let C := 32768 * (32 * Y) ^ 8
  have hK : 0 < K := primorial_pos Y
  have hYX : Y ≤ X := prime_progression_scale_ge Y
  have hX : 2 * K ≤ X := prime_progression_scale_twice_primorial Y
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d ∣ K := by
    intro d hd
    have h := prime_subset_products_valid Y 24 (by decide) d hd
    exact ⟨h.1, h.2.1⟩
  have hAP : ∀ d ∈ D, (X : ℝ) / (2 * d.totient * Real.log X) ≤ (primesOneMod X d).card := by
    intro d hd
    apply hN X (hYN.trans hYX) d (hD d hd).1
    have hdY := (prime_subset_products_valid Y 24 (by decide) d hd).2.2
    have hlog := (log_prime_progression_scale_bounds Y (by omega)).1
    exact (show (d : ℝ) ≤ (Y : ℝ) ^ 24 by exact_mod_cast hdY).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg Y) hlog 24)
  obtain ⟨n, hKn, hnX, _hdiv, hCn⟩ := shifted_prime_spike_of_many_progressions K X C D
    hK hX hD hAP (prime_subset_products_dominate Y hY hbig)
  have hYn : Y ≤ n := (show Y ≤ K from le_primorial_self).trans hKn
  refine ⟨n, hYB.trans hYn, by omega, ?_⟩
  have hc := shifted_prime_requirement_below_scale Y n (by omega) hYn hnX
  exact hc.trans (by exact_mod_cast hCn.le)

end Erdos345
