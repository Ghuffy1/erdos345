import Erdos345.DiscreteOscillation
import Erdos345.CyclotomicExpansion

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

theorem unit_geometric_sum_norm_le_length (z : ℂ) (hz : ‖z‖ = 1) (L : ℕ) :
    ‖∑ n ∈ range L, z ^ n‖ ≤ L := by
  calc
    _ ≤ ∑ n ∈ range L, ‖z ^ n‖ := norm_sum_le _ _
    _ = (L : ℝ) := by simp only [norm_pow, hz, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem unit_norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (L : ℕ) :
    ‖z ^ L - 1‖ ≤ L * ‖z - 1‖ := by
  rw [← geom_sum_mul z L, norm_mul]
  exact mul_le_mul_of_nonneg_right (unit_geometric_sum_norm_le_length z hz L) (norm_nonneg _)

/-- An elementary separation bound. It avoids choosing arguments of roots
of unity and suffices for the polynomial-size Gram interval requirement. -/
theorem root_of_unity_separation (z : ℂ) (hz : ‖z‖ = 1)
    (L : ℕ) (hL : 0 < L) (hpow : z ^ L = 1) (hne : z ≠ 1) :
    1 / (L : ℝ) ≤ ‖z - 1‖ := by
  have hsum : ∑ n ∈ range L, z ^ n = 0 := by rw [geom_sum_eq hne, hpow, sub_self, zero_div]
  have heq : (L : ℂ) = ∑ n ∈ range L, (1 - z ^ n) := by
    rw [sum_sub_distrib, hsum]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, sub_zero]
  have hR : (0 : ℝ) < L := by exact_mod_cast hL
  have hbound : (L : ℝ) ≤ (L : ℝ) * (L * ‖z - 1‖) := by
    calc
      (L : ℝ) = ‖(L : ℂ)‖ := (Complex.norm_natCast L).symm
      _ = ‖∑ n ∈ range L, (1 - z ^ n)‖ := by rw [heq]
      _ ≤ ∑ n ∈ range L, ‖1 - z ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range L, (L : ℝ) * ‖z - 1‖ := by
        apply sum_le_sum
        intro n hn
        rw [norm_sub_rev]
        exact (unit_norm_pow_sub_one_le z hz n).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hn).le) (norm_nonneg _))
      _ = _ := by simp
  apply (div_le_iff₀ hR).mpr
  nlinarith

theorem distinct_roots_ratio_separation (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hxp : x ^ m = 1) (hyp : y ^ n = 1)
    (hne : x ≠ y) :
    1 / ((m * n : ℕ) : ℝ) ≤ ‖conj x * y - 1‖ := by
  have hnorm : ‖conj x * y‖ = 1 := by rw [norm_mul, norm_conj, hx, hy, one_mul]
  have hxp' : x ^ (m * n) = 1 := by rw [pow_mul, hxp, one_pow]
  have hyp' : y ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, hyp, one_pow]
  have hpow : (conj x * y) ^ (m * n) = 1 := by
    rw [mul_pow, ← map_pow, hxp', hyp', map_one, one_mul]
  have hunit : x * conj x = 1 := by rw [Complex.mul_conj', hx]; norm_num
  have hne' : conj x * y ≠ 1 := by
    intro heq
    have h := congrArg (fun u : ℂ => x * u) heq
    rw [← mul_assoc, hunit, one_mul, mul_one] at h
    exact hne h.symm
  exact root_of_unity_separation _ hnorm (m * n) (Nat.mul_pos hm hn) hpow hne'

theorem cyclotomic_root_separation (N : ℕ) (i j : CyclotomicRootIndex (Icc 1 N))
    (hij : i ≠ j) :
    1 / ((N : ℝ) ^ 2) ≤ ‖conj (cyclotomicRootValue i) * cyclotomicRootValue j - 1‖ := by
  have hi := isPrimitiveRoot_of_mem_primitiveRoots i.2.property
  have hj := isPrimitiveRoot_of_mem_primitiveRoots j.2.property
  have hiN := mem_Icc.mp i.1.property
  have hjN := mem_Icc.mp j.1.property
  have hm : 0 < (i.1 : ℕ) := hiN.1
  have hn : 0 < (j.1 : ℕ) := hjN.1
  have hne : cyclotomicRootValue i ≠ cyclotomicRootValue j :=
    fun heq => hij ((cyclotomicRootValue_injective _) heq)
  have hsep := distinct_roots_ratio_separation _ _
    ((hi.isOfFinOrder (Nat.ne_of_gt hm)).norm_eq_one)
    ((hj.isOfFinOrder (Nat.ne_of_gt hn)).norm_eq_one)
    i.1 j.1 hm hn hi.pow_eq_one hj.pow_eq_one hne
  have hpos : (0 : ℝ) < ((i.1 : ℕ) * (j.1 : ℕ) : ℕ) := by exact_mod_cast Nat.mul_pos hm hn
  have hle : (((i.1 : ℕ) * (j.1 : ℕ) : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    simpa only [pow_two, Nat.cast_mul] using
      (by exact_mod_cast (Nat.mul_le_mul hiN.2 hjN.2) :
        (((i.1 : ℕ) * (j.1 : ℕ) : ℕ) : ℝ) ≤ (N : ℝ) * N)
  exact (one_div_le_one_div_of_le hpos hle).trans hsep

end Erdos345
