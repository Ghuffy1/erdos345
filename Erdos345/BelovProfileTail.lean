import Erdos345.BelovProfileLevels
import Erdos345.DyadicFifthMoment

namespace Erdos345

theorem belovProfileHead_bound (q N r : ℕ) (hq : 256 ≤ q) :
    (∑ j ∈ Finset.range (r - 1), belovProfileLevel q N j) ≤
      (5 / 2 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 := by
  have hpoint : ∀ j ∈ Finset.range (r - 1), belovProfileLevel q N j ≤
      (5 / 2 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 4 := by
    intro j hj
    have hjr : ((j + 1 : ℕ) : ℝ) ≤ r := by
      exact_mod_cast (show j + 1 ≤ r by have := Finset.mem_range.mp hj; omega)
    exact (belovProfileLevel_le_count q N j hq).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjr 4) (by positivity))
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hrr : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hm := mul_le_mul_of_nonneg_right hrr
    (show 0 ≤ (5 / 2 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 4 by positivity)
  nlinarith

theorem belovProfileTail_bound (q N r : ℕ) (hq : 256 ≤ q) (hr : 3 ≤ r) :
    (∑' n : ℕ, belovProfileLevel q N (n + (r - 1))) ≤
      ((5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) / 2 ^ r) * (36 * (r : ℝ) ^ 5) := by
  let A : ℝ := (5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) / 2 ^ r
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpoint : ∀ n : ℕ, belovProfileLevel q N (n + (r - 1)) ≤
      A * (((r : ℝ) + n) ^ 5 / 2 ^ n) := by
    intro n
    have hb := belovProfileLevel_le_reciprocal q N (n + (r - 1)) hq
    have heq : n + (r - 1) + 1 = n + r := by omega
    rw [heq] at hb
    convert hb using 1
    dsimp only [A]
    rw [pow_add]
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℕ => n + (r - 1)) := by
    intro a b hab
    change a + (r - 1) = b + (r - 1) at hab
    omega
  have hs := (summable_belovProfileLevels q N).comp_injective hinj
  have hb := hs.tsum_le_tsum hpoint ((summable_shift_fifth_div_two r).mul_left A)
  rw [tsum_mul_left] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (dyadic_fifth_shift_bound r hr) hA)

theorem belovProfile_split_bound (q N r : ℕ) (hq : 256 ≤ q) (hr : 3 ≤ r) :
    belovProfileMajorant q N ≤ 1 + (5 / 2 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 +
      ((5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) / 2 ^ r) * (36 * (r : ℝ) ^ 5) := by
  rw [belovProfileMajorant_eq_levels,
    ← (summable_belovProfileLevels q N).sum_add_tsum_nat_add (r - 1)]
  have hhead := belovProfileHead_bound q N r hq
  have htail := belovProfileTail_bound q N r hq hr
  have hbase : min (1 : ℝ) (N : ℝ) ≤ 1 := min_le_left _ _
  linarith

theorem belovProfile_linear_bound (q N : ℕ) (hq : 256 ≤ q) :
    belovProfileMajorant q N ≤ 1 + (5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) * 1082 := by
  let A : ℝ := (5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ)
  have hpoint : ∀ j : ℕ, belovProfileLevel q N j ≤
      A * (((j + 1 : ℕ) : ℝ) ^ 5 / 2 ^ (j + 1)) := by
    intro j
    convert belovProfileLevel_le_reciprocal q N j hq using 1
    dsimp only [A]
    ring
  have hinj : Function.Injective (fun j : ℕ => j + 1) := by
    intro a b hab
    change a + 1 = b + 1 at hab
    omega
  have hs := ((summable_nat_pow_div_two 5).comp_injective hinj).mul_left A
  have hb := (summable_belovProfileLevels q N).tsum_le_tsum hpoint hs
  rw [tsum_mul_left, tsum_succ_fifth_div_two] at hb
  rw [belovProfileMajorant_eq_levels]
  have hbase : min (1 : ℝ) (N : ℝ) ≤ 1 := min_le_left _ _
  dsimp only [A] at hb
  linarith

end Erdos345
