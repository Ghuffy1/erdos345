import Erdos345.BelovDyadicFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos345

theorem belovLevelPrimes_prime {q j p : ℕ} (hp : p ∈ belovLevelPrimes q j) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_of_mem_erase hp)).2

theorem belovLevelPrimes_three_le {q j p : ℕ} (hp : p ∈ belovLevelPrimes q j) : 3 ≤ p := by
  have htwo := (belovLevelPrimes_prime hp).two_le
  have hne : p ≠ 2 := (Finset.mem_erase.mp hp).1
  omega

theorem belovSineLevel_nonneg_of_phase_le_six (q j : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hphase : x / 2 ^ j ≤ 6) : 0 ≤ belovSineLevel q j x := by
  change 0 ≤ ∑ p ∈ belovLevelPrimes q j, scaledSineBlock p (belovMultiplicity j) (x / 2 ^ j)
  apply Finset.sum_nonneg
  intro p hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast belovLevelPrimes_three_le hp
  exact scaledSineBlock_nonneg p _ (by have := belovLevelPrimes_three_le hp; omega)
    (by positivity) (by linarith)

theorem belovSineLevel_zero_ge_neg_three (q : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hx8 : x ≤ 8) : -3 ≤ belovSineLevel q 0 x := by
  classical
  change -3 ≤ ∑ p ∈ belovLevelPrimes q 0, scaledSineBlock p (belovMultiplicity 0) (x / 2 ^ 0)
  simp only [belovMultiplicity_zero, pow_zero, div_one]
  have hrest : 0 ≤ ∑ p ∈ (belovLevelPrimes q 0).erase 3, scaledSineBlock p 1 x := by
    apply Finset.sum_nonneg
    intro p hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    have hp4 : 4 ≤ p := by have := belovLevelPrimes_three_le hmem; omega
    have hp4R : (4 : ℝ) ≤ p := by exact_mod_cast hp4
    exact scaledSineBlock_nonneg p 1 (by omega) hx (by linarith)
  by_cases hthree : 3 ∈ belovLevelPrimes q 0
  · have heq := Finset.sum_erase_add (belovLevelPrimes q 0) (fun p => scaledSineBlock p 1 x) hthree
    have hb := neg_abs_le (scaledSineBlock 3 1 x)
    have hab := scaledSineBlock_abs_le 3 1 x
    norm_num at hab
    linarith
  · rw [Finset.erase_eq_of_notMem hthree] at hrest
    linarith

theorem belovSineLevel_six_gt_argument (q : ℕ) (hq : 3 ≤ q) {x : ℝ}
    (hx : 0 < x) (hx8 : x ≤ 8) : x < belovSineLevel q 6 x := by
  have h131 : 131 ∈ belovLevelPrimes q 6 := by
    apply Finset.mem_erase.mpr
    refine ⟨by decide, Nat.mem_primesLE.mpr ⟨?_, by norm_num⟩⟩
    nlinarith
  have hvpos : 0 < belovMultiplicity 6 := by unfold belovMultiplicity; omega
  have hvle : (belovMultiplicity 6 : ℝ) ≤ 7 := by exact_mod_cast belovMultiplicity_le 6
  have hphase : (belovMultiplicity 6 : ℝ) * (x / 2 ^ 6) ≤ 1 := by
    norm_num
    nlinarith
  have hb := scaledSineBlock_small_lower 131 (belovMultiplicity 6) (by norm_num) hvpos
    (show 0 < x / 2 ^ 6 by positivity) hphase
  have hs : scaledSineBlock 131 (belovMultiplicity 6) (x / 2 ^ 6) ≤ belovSineLevel q 6 x := by
    change scaledSineBlock 131 (belovMultiplicity 6) (x / 2 ^ 6) ≤
      ∑ p ∈ belovLevelPrimes q 6, scaledSineBlock p (belovMultiplicity 6) (x / 2 ^ 6)
    refine Finset.single_le_sum (f := fun p : ℕ => scaledSineBlock p (belovMultiplicity 6) (x / 2 ^ 6)) ?_ h131
    intro p hp
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast belovLevelPrimes_three_le hp
    exact scaledSineBlock_nonneg p _ (by have := belovLevelPrimes_three_le hp; omega)
      (by positivity) (by norm_num; linarith)
  have hv1 : (1 : ℝ) ≤ belovMultiplicity 6 := by exact_mod_cast hvpos
  have hpi := Real.pi_lt_four
  have hpipos := Real.pi_pos
  have hconst : 1 < 2 / Real.pi * (belovMultiplicity 6 : ℝ) ^ 2 * 131 / 64 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    simp only [one_mul]
    calc
      64 < 2 * (belovMultiplicity 6 : ℝ) ^ 2 * 131 / Real.pi := by
        apply (lt_div_iff₀ hpipos).mpr
        nlinarith [sq_nonneg ((belovMultiplicity 6 : ℝ) - 1)]
      _ = _ := by ring
  have hmul := mul_lt_mul_of_pos_right hconst hx
  norm_num at hb
  nlinarith

theorem belovSineTotal_pos_upto_eight (q : ℕ) (hq : 3 ≤ q) {x : ℝ}
    (hx : 0 < x) (hx8 : x ≤ 8) : 0 < belovSineTotal q x := by
  by_cases hx1 : x ≤ 1
  · exact belovSineTotal_pos_small q hq hx hx1
  have hlevel := belovSineLevel_six_gt_argument q hq hx hx8
  have hsin : -1 ≤ Real.sin (Real.pi * x) := Real.neg_one_le_sin _
  by_cases hx6 : x ≤ 6
  · have hn : ∀ j, 0 ≤ belovSineLevel q j x := by
      intro j
      apply belovSineLevel_nonneg_of_phase_le_six q j hx.le
      have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have hsum := (summable_belovSineLevels q x).sum_le_tsum ({6} : Finset ℕ) (fun j _ => hn j)
    simp only [Finset.sum_singleton] at hsum
    unfold belovSineTotal
    linarith
  · have hn : ∀ j, j ≠ 0 → 0 ≤ belovSineLevel q j x := by
      intro j hj
      apply belovSineLevel_nonneg_of_phase_le_six q j hx.le
      have hp : (2 : ℝ) ≤ 2 ^ j := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ j by omega)
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have houtside : ∀ j, j ∉ ({0, 6} : Finset ℕ) → 0 ≤ belovSineLevel q j x := by
      intro j hj
      apply hn j
      intro heq
      subst j
      exact hj (by simp)
    have hsum := (summable_belovSineLevels q x).sum_le_tsum ({0, 6} : Finset ℕ) houtside
    simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ {6}), Finset.sum_singleton] at hsum
    have hzero := belovSineLevel_zero_ge_neg_three q hx.le hx8
    unfold belovSineTotal
    linarith

end Erdos345
