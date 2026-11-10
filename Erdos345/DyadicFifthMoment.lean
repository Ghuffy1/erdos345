import Erdos345.DyadicPolynomialSummability
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Erdos345

theorem hasSum_nat_pow_div_two (d : ℕ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ d / 2 ^ n)
      (∑ j ∈ Finset.range (d + 1),
        (Nat.stirlingSecond d j : ℝ) * (j.factorial : ℝ) * (1 / 2 : ℝ) ^ j /
          (1 - (1 / 2 : ℝ)) ^ (j + 1)) := by
  have h := hasSum_pow_mul_geometric_of_norm_lt_one (𝕜 := ℝ) d (r := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  funext n
  simp only [div_eq_mul_inv, one_mul, inv_pow]

theorem hasSum_shift_three_fifth_div_two :
    HasSum (fun n : ℕ => ((n : ℝ) + 3) ^ 5 / 2 ^ n) 8588 := by
  have h0 := hasSum_nat_pow_div_two 0
  have h1 := hasSum_nat_pow_div_two 1
  have h2 := hasSum_nat_pow_div_two 2
  have h3 := hasSum_nat_pow_div_two 3
  have h4 := hasSum_nat_pow_div_two 4
  have h5 := hasSum_nat_pow_div_two 5
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial] at h0 h1 h2 h3 h4 h5
  have h := ((((h5.add (h4.mul_left 15)).add (h3.mul_left 90)).add
    (h2.mul_left 270)).add (h1.mul_left 405)).add (h0.mul_left 243)
  convert h using 1
  · funext n
    ring
  · norm_num

theorem hasSum_nat_fifth_div_two :
    HasSum (fun n : ℕ => (n : ℝ) ^ 5 / 2 ^ n) 1082 := by
  have h := hasSum_nat_pow_div_two 5
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial] at h
  exact h

theorem tsum_succ_fifth_div_two :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 5 / 2 ^ (n + 1)) = 1082 := by
  have h := hasSum_nat_fifth_div_two.summable.sum_add_tsum_nat_add 1
  rw [hasSum_nat_fifth_div_two.tsum_eq] at h
  simpa using h

theorem summable_shift_fifth_div_two (r : ℕ) :
    Summable (fun n : ℕ => ((r : ℝ) + n) ^ 5 / 2 ^ n) := by
  have hinj : Function.Injective (fun n : ℕ => r + n) := fun _ _ h => Nat.add_left_cancel h
  have h := (summable_nat_pow_div_two 5).comp_injective hinj
  have hm := h.mul_left ((2 : ℝ) ^ r)
  apply hm.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [pow_add, Nat.cast_add]
  field_simp

theorem dyadic_fifth_shift_bound (r : ℕ) (hr : 3 ≤ r) :
    (∑' n : ℕ, (((r : ℝ) + n) ^ 5 / 2 ^ n)) ≤ 36 * (r : ℝ) ^ 5 := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  let C : ℝ := (r : ℝ) ^ 5 / 3 ^ 5
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint : ∀ n : ℕ, ((r : ℝ) + n) ^ 5 / 2 ^ n ≤
      C * (((n : ℝ) + 3) ^ 5 / 2 ^ n) := by
    intro n
    have hbase : (r : ℝ) + n ≤ (r : ℝ) / 3 * ((n : ℝ) + 3) := by
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) - 3 by linarith) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hp := pow_le_pow_left₀ (show 0 ≤ (r : ℝ) + n by positivity) hbase 5
    have hd := div_le_div_of_nonneg_right hp (show 0 ≤ (2 : ℝ) ^ n by positivity)
    convert hd using 1
    dsimp only [C]
    ring
  have hs := hasSum_shift_three_fifth_div_two.summable.mul_left C
  have hrSum : Summable (fun n : ℕ => ((r : ℝ) + n) ^ 5 / 2 ^ n) := by
    apply hs.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint n
  have hb := hrSum.tsum_le_tsum hpoint hs
  rw [tsum_mul_left, hasSum_shift_three_fifth_div_two.tsum_eq] at hb
  dsimp only [C] at hb
  nlinarith [pow_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) 5]

end Erdos345
