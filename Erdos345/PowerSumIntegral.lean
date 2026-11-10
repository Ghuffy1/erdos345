import Erdos345.SamplingRatio
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos345

theorem positive_power_sum_bound (U k : ℕ) :
    (∑ n ∈ Finset.Icc 1 U, (n : ℝ) ^ k) ≤
      ((U + 1 : ℕ) : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ k) (Set.Icc ((1 : ℕ) : ℝ) ((U + 1 : ℕ) : ℝ)) := by
    intro a ha b _ hab
    exact pow_le_pow_left₀ (by linarith [ha.1]) hab k
  have hi := hmono.sum_le_integral_Ico (show 1 ≤ U + 1 by omega)
  simp only [Nat.cast_one] at hi
  rw [integral_pow, one_pow] at hi
  have hi' : (∑ n ∈ Finset.Ico 1 (U + 1), (n : ℝ) ^ k) ≤
      (((U + 1 : ℕ) : ℝ) ^ (k + 1) - 1) / ((k + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hi
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hfinal : (∑ n ∈ Finset.Ico 1 (U + 1), (n : ℝ) ^ k) ≤
      ((U + 1 : ℕ) : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right
      (show ((U + 1 : ℕ) : ℝ) ^ (k + 1) - 1 ≤ ((U + 1 : ℕ) : ℝ) ^ (k + 1) by linarith) hk.le
    exact hi'.trans hdiv
  simpa only [Finset.Ico_add_one_right_eq_Icc] using hfinal

theorem unreservedEndpoint_add_one_le (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    unreservedEndpoint N k + 1 ≤ N := by
  have hdiv : 1 ≤ N / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkN)
  have hle : N / k ≤ N := Nat.div_le_self N k
  unfold unreservedEndpoint
  omega

theorem unreserved_power_sum_bound (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) (d : ℕ) :
    (∑ n ∈ unreservedPopulation N k, (n : ℝ) ^ d) ≤
      (N : ℝ) ^ (d + 1) / ((d + 1 : ℕ) : ℝ) := by
  have hsub : unreservedPopulation N k ⊆ Finset.Icc 1 (unreservedEndpoint N k) :=
    Finset.sdiff_subset
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => pow_nonneg (Nat.cast_nonneg (α := ℝ) n) d)
  have hpow : ((unreservedEndpoint N k + 1 : ℕ) : ℝ) ^ (d + 1) ≤ (N : ℝ) ^ (d + 1) := by
    gcongr
    exact_mod_cast unreservedEndpoint_add_one_le N k hk hkN
  exact hsum.trans ((positive_power_sum_bound (unreservedEndpoint N k) d).trans
    (div_le_div_of_nonneg_right hpow (by positivity)))

theorem unreserved_power_square_sum_bound (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    (∑ n ∈ unreservedPopulation N k, ((n : ℝ) ^ k) ^ 2) ≤ (N : ℝ) ^ (2 * k + 1) := by
  have hsum := unreserved_power_sum_bound N k hk hkN (2 * k)
  have hden : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
  have hdiv := div_le_self (pow_nonneg (Nat.cast_nonneg (α := ℝ) N) (2 * k + 1)) hden
  calc
    _ = ∑ n ∈ unreservedPopulation N k, (n : ℝ) ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [← pow_mul, Nat.mul_comm k 2]
    _ ≤ _ := hsum.trans hdiv

end Erdos345
