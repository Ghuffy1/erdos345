import Erdos345.BelovBoundedPositivity
import Erdos345.PrimeSineCancellation
import Erdos345.BelovPrimeMass

namespace Erdos345

theorem belovSineLevel_lower_log (q j : ℕ) (hq : 256 ≤ q) {x : ℝ} (hx : 0 ≤ x) :
    -(6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * max 0 (Real.log (x / 2 ^ j))) ≤
      belovSineLevel q j x := by
  classical
  let t : ℝ := x / 2 ^ j
  by_cases ht : 1 < t
  · let A := q * (j + 1) ^ 2
    let P : Finset ℕ := (belovLevelPrimes q j).filter (fun p : ℕ => (p : ℝ) < t / 2)
    have hA : 4 ≤ A := by
      dsimp only [A]
      nlinarith [Nat.one_le_pow 2 (j + 1) (by omega : 1 ≤ j + 1)]
    have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
    have hv : (belovMultiplicity j : ℝ) / Real.log (A : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hlogA).mpr
      have h := belovMultiplicity_twice_le_log_scale q j hq
      change 2 * (belovMultiplicity j : ℝ) ≤ Real.log (A : ℝ) at h
      linarith
    have hsum := sum_abs_prime_sine_bound P A (belovMultiplicity j) t hA ht
      (fun p hp => belovLevelPrimes_prime (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_Icc.mp (belovLevelPrimes_subset q j (Finset.mem_filter.mp hp).1)).2)
      (fun _ hp => (Finset.mem_filter.mp hp).2)
    have hlogt : 0 < Real.log t := Real.log_pos ht
    have hcap : (∑ p ∈ P, |scaledSineBlock p (belovMultiplicity j) t|) ≤
        6 * (A : ℝ) * Real.log t := by
      have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ 4 * (A : ℝ) * Real.log t by positivity)
      nlinarith
    have hrest : 0 ≤ ∑ p ∈ (belovLevelPrimes q j).filter (fun p : ℕ => ¬(p : ℝ) < t / 2),
        scaledSineBlock p (belovMultiplicity j) t := by
      apply Finset.sum_nonneg
      intro p hp
      obtain ⟨hp, hnot⟩ := Finset.mem_filter.mp hp
      exact scaledSineBlock_nonneg p _ (belovLevelPrimes_prime hp).pos
        (by dsimp only [t]; positivity) (by linarith)
    have hneg : -(6 * (A : ℝ) * Real.log t) ≤ ∑ p ∈ P, scaledSineBlock p (belovMultiplicity j) t := by
      calc
        _ ≤ -(∑ p ∈ P, |scaledSineBlock p (belovMultiplicity j) t|) := neg_le_neg hcap
        _ = ∑ p ∈ P, -|scaledSineBlock p (belovMultiplicity j) t| :=
          (Finset.sum_neg_distrib (fun p => |scaledSineBlock p (belovMultiplicity j) t|)).symm
        _ ≤ _ := Finset.sum_le_sum (fun p _ => neg_abs_le _)
    have hsplit := Finset.sum_filter_add_sum_filter_not (belovLevelPrimes q j)
      (fun p : ℕ => (p : ℝ) < t / 2) (fun p => scaledSineBlock p (belovMultiplicity j) t)
    have htotal : -(6 * (A : ℝ) * Real.log t) ≤ belovSineLevel q j x := by
      change -(6 * (A : ℝ) * Real.log t) ≤ ∑ p ∈ belovLevelPrimes q j, scaledSineBlock p (belovMultiplicity j) t
      dsimp only [P] at hneg
      linarith
    have heq : -(6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * max 0 (Real.log t)) =
        -(6 * (A : ℝ) * Real.log t) := by
      rw [max_eq_right hlogt.le]
      dsimp only [A]
      push_cast
      ring
    change -(6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * max 0 (Real.log t)) ≤ _
    rw [heq]
    exact htotal
  · have hn := belovSineLevel_nonneg_of_phase_le_six q j hx (show x / 2 ^ j ≤ 6 by dsimp only [t] at ht; linarith)
    have hm : 0 ≤ 6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * max 0 (Real.log (x / 2 ^ j)) := by positivity
    linarith

theorem dyadic_log_envelope (r j : ℕ) (hj : j ≤ r) {x : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ (2 : ℝ) ^ r) :
    max 0 (Real.log (x / 2 ^ j)) ≤ ((r : ℝ) - j) * Real.log 2 := by
  have hrj : 0 ≤ (r : ℝ) - j := sub_nonneg.mpr (by exact_mod_cast hj)
  have hnon := mul_nonneg hrj (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  by_cases hxpos : 0 < x
  · have hb := Real.log_le_log (show 0 < x / 2 ^ j by positivity)
      (div_le_div_of_nonneg_right hxr (by positivity : (0 : ℝ) ≤ 2 ^ j))
    have heq : Real.log ((2 : ℝ) ^ r / 2 ^ j) = (r : ℝ) * Real.log 2 - j * Real.log 2 := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [heq] at hb
    apply max_le hnon
    nlinarith
  · have hz : x = 0 := by linarith
    simp only [hz, zero_div, Real.log_zero, max_self]
    exact hnon

theorem weighted_square_prefix (r n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2 * ((r : ℝ) - j)) =
      ((r : ℝ) + 1) * n * (n + 1) * (2 * n + 1) / 6 - ((n : ℝ) * (n + 1)) ^ 2 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem weighted_square_triangle (r : ℕ) :
    (∑ j ∈ Finset.range r, ((j : ℝ) + 1) ^ 2 * ((r : ℝ) - j)) =
      (r : ℝ) * (r + 1) ^ 2 * (r + 2) / 12 := by
  rw [weighted_square_prefix]
  ring

theorem belovSinePrefix_lower (q r : ℕ) (hq : 256 ≤ q) {x : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ (2 : ℝ) ^ r) :
    -((q : ℝ) / 2 * Real.log 2 * r * (r + 1) ^ 2 * (r + 2)) ≤
      ∑ j ∈ Finset.range r, belovSineLevel q j x := by
  have hpoint : ∀ j ∈ Finset.range r,
      -(6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * ((r : ℝ) - j) * Real.log 2) ≤ belovSineLevel q j x := by
    intro j hj
    have hlog := dyadic_log_envelope r j (Nat.le_of_lt (Finset.mem_range.mp hj)) hx hxr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 by positivity)
    have hl := belovSineLevel_lower_log q j hq hx
    nlinarith
  calc
    _ = -(6 * (q : ℝ) * Real.log 2 * ∑ j ∈ Finset.range r, ((j : ℝ) + 1) ^ 2 * ((r : ℝ) - j)) := by
      rw [weighted_square_triangle]
      ring
    _ = ∑ j ∈ Finset.range r, -(6 * (q : ℝ) * ((j : ℝ) + 1) ^ 2 * ((r : ℝ) - j) * Real.log 2) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := Finset.sum_le_sum hpoint

theorem belovSineTotal_lower_with_level (q r : ℕ) (hq : 256 ≤ q) {x : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ (2 : ℝ) ^ r) :
    -1 - ((q : ℝ) / 2 * Real.log 2 * r * (r + 1) ^ 2 * (r + 2)) +
      belovSineLevel q r x ≤ belovSineTotal q x := by
  have hp : (2 : ℝ) ^ r ≤ 2 ^ ((r + 1) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have ht := belovSineTotal_ge_prefix q (r + 1) hx (hxr.trans hp)
  rw [Finset.sum_range_succ] at ht
  have hl := belovSinePrefix_lower q r hq hx hxr
  have hs := Real.neg_one_le_sin (Real.pi * x)
  linarith

end Erdos345
