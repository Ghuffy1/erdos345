import Erdos345.BelovBoundedPositivity
import Erdos345.PrimeCountingUpper

namespace Erdos345

theorem belovMultiplicity_pos (r : ℕ) : 0 < belovMultiplicity r := by
  unfold belovMultiplicity
  omega

theorem belovMultiplicity_mono : Monotone belovMultiplicity := by
  intro a b hab
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < ((a + 1 : ℕ) : ℝ))
    (show ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) by exact_mod_cast (show a + 1 ≤ b + 1 by omega))
  have hf := Nat.floor_mono hl
  unfold belovMultiplicity
  omega

theorem exists_belov_safe_level {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℕ, (belovMultiplicity r : ℝ) * x ≤ (2 : ℝ) ^ r := by
  have ht : Filter.Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ) / 2 ^ r) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using (summable_succ_pow_div_two 1).tendsto_atTop_zero
  have htx : Filter.Tendsto (fun r : ℕ => x * (((r + 1 : ℕ) : ℝ) / 2 ^ r)) Filter.atTop (nhds 0) := by
    simpa using ht.const_mul x
  have he := htx.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp he
  refine ⟨r, ?_⟩
  have hb : (belovMultiplicity r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast belovMultiplicity_le r
  have hm := mul_le_mul_of_nonneg_right hb hx
  have hh := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ r by positivity)).mp (show x * ((r + 1 : ℕ) : ℝ) / 2 ^ r < 1 by simpa only [mul_div_assoc] using hr r le_rfl)
  nlinarith

theorem belovMultiplicity_four_ge_two : 2 ≤ belovMultiplicity 4 := by
  have hlog : (1 : ℝ) ≤ Real.log 5 := by
    have h45 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 5)
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4] at h45
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hf : 1 ≤ ⌊Real.log (5 : ℝ)⌋₊ := Nat.le_floor (by simpa using hlog)
  norm_num [belovMultiplicity]
  omega

theorem exists_belov_balanced_level {x : ℝ} (hx : 8 < x) :
    ∃ r : ℕ, 5 ≤ r ∧ x ≤ (2 : ℝ) ^ r ∧
      1 / 2 ≤ (belovMultiplicity r : ℝ) * (x / 2 ^ r) ∧
      (belovMultiplicity r : ℝ) * (x / 2 ^ r) ≤ 1 := by
  have hx0 : 0 ≤ x := by linarith
  obtain h := exists_belov_safe_level hx0
  let r := Nat.find h
  have hs : (belovMultiplicity r : ℝ) * x ≤ (2 : ℝ) ^ r := Nat.find_spec h
  have hr5 : 5 ≤ r := by
    by_contra hnot
    have hr4 : r ≤ 4 := by omega
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr4
    have hv1 : (1 : ℝ) ≤ belovMultiplicity r := by exact_mod_cast belovMultiplicity_pos r
    by_cases hr3 : r ≤ 3
    · have hp3 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr3
      norm_num at hp3
      nlinarith
    · have heq : r = 4 := by omega
      rw [heq] at hs
      have hv2 : (2 : ℝ) ≤ belovMultiplicity 4 := by exact_mod_cast belovMultiplicity_four_ge_two
      norm_num at hs
      nlinarith
  have hr0 : 0 < r := by omega
  have hprev : ¬ (belovMultiplicity (r - 1) : ℝ) * x ≤ (2 : ℝ) ^ (r - 1) :=
    Nat.find_min h (show r - 1 < Nat.find h by dsimp only [r]; omega)
  have hvmono : (belovMultiplicity (r - 1) : ℝ) ≤ belovMultiplicity r := by
    exact_mod_cast belovMultiplicity_mono (show r - 1 ≤ r by omega)
  have hpow : (2 : ℝ) ^ r = 2 * 2 ^ (r - 1) := by
    calc
      _ = (2 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have hv1 : (1 : ℝ) ≤ belovMultiplicity r := by exact_mod_cast belovMultiplicity_pos r
  refine ⟨r, hr5, ?_, ?_, ?_⟩
  · nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ (show (0 : ℝ) < 2 ^ r by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hvmono hx0
    linarith
  · rw [← mul_div_assoc]
    exact (div_le_one (by positivity)).mpr hs

end Erdos345
