import Erdos345.DiscreteGram
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Module

namespace Erdos345

open Finset

theorem unit_geometric_sum_norm_le (z : ℂ) (hz : ‖z‖ = 1)
    (δ : ℝ) (hδ : 0 < δ) (hsep : δ ≤ ‖z - 1‖) (L : ℕ) :
    ‖∑ n ∈ range L, z ^ n‖ ≤ 2 / δ := by
  have hne : z ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖z ^ L - 1‖ ≤ 2 := by
    have h := norm_sub_le (z ^ L) (1 : ℂ)
    simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using h
  exact div_le_div₀ (by positivity) hnum hδ hsep

/-- Abel summation with a quantitative separation from the unit frequency. -/
theorem oscillatory_sum_norm_le_variation (a : ℕ → ℂ) (z : ℂ) (hz : ‖z‖ = 1)
    (δ : ℝ) (hδ : 0 < δ) (hsep : δ ≤ ‖z - 1‖) (L : ℕ) :
    ‖∑ n ∈ range L, a n * z ^ n‖ ≤
      (‖a (L - 1)‖ + ∑ n ∈ range (L - 1), ‖a (n + 1) - a n‖) * (2 / δ) := by
  have hAbel := sum_range_by_parts a (fun n => z ^ n) L
  simp only [smul_eq_mul] at hAbel
  rw [hAbel]
  calc
    _ ≤ ‖a (L - 1) * ∑ n ∈ range L, z ^ n‖ +
        ‖∑ n ∈ range (L - 1), (a (n + 1) - a n) * ∑ j ∈ range (n + 1), z ^ j‖ :=
      norm_sub_le _ _
    _ ≤ ‖a (L - 1)‖ * (2 / δ) +
        ∑ n ∈ range (L - 1), ‖a (n + 1) - a n‖ * (2 / δ) := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (unit_geometric_sum_norm_le z hz δ hδ hsep L) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        apply sum_le_sum
        intro n _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (unit_geometric_sum_norm_le z hz δ hδ hsep (n + 1))
          (norm_nonneg _)
    _ = _ := by rw [← sum_mul, add_mul]

theorem oscillatory_sum_norm_le_of_step_bound (a : ℕ → ℂ) (z : ℂ) (hz : ‖z‖ = 1)
    (δ : ℝ) (hδ : 0 < δ) (hsep : δ ≤ ‖z - 1‖)
    (L : ℕ) (hL : 0 < L) (B V : ℝ) (hV : 0 ≤ V)
    (hB : ‖a (L - 1)‖ ≤ B)
    (hstep : ∀ n < L - 1, ‖a (n + 1) - a n‖ ≤ V / L) :
    ‖∑ n ∈ range L, a n * z ^ n‖ ≤ (B + V) * (2 / δ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : (∑ n ∈ range (L - 1), ‖a (n + 1) - a n‖) ≤ V := by
    calc
      _ ≤ ∑ _n ∈ range (L - 1), V / L :=
        sum_le_sum (fun n hn => hstep n (mem_range.mp hn))
      _ = ((L - 1 : ℕ) : ℝ) * (V / L) := by simp
      _ ≤ (L : ℝ) * (V / L) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hV hLR.le)
        exact_mod_cast Nat.sub_le L 1
      _ = V := by field_simp
  exact (oscillatory_sum_norm_le_variation a z hz δ hδ hsep L).trans
    (mul_le_mul_of_nonneg_right (add_le_add hB hsum) (div_nonneg (by norm_num) hδ.le))

theorem product_step_norm_le (a b : ℕ → ℂ) (n : ℕ) :
    ‖a (n + 1) * b (n + 1) - a n * b n‖ ≤
      ‖a (n + 1)‖ * ‖b (n + 1) - b n‖ + ‖b n‖ * ‖a (n + 1) - a n‖ := by
  have heq : a (n + 1) * b (n + 1) - a n * b n =
      a (n + 1) * (b (n + 1) - b n) + b n * (a (n + 1) - a n) := by ring
  rw [heq]
  simpa only [norm_mul] using norm_add_le
    (a (n + 1) * (b (n + 1) - b n)) (b n * (a (n + 1) - a n))

end Erdos345
