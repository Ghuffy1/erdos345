import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos345

def divisorCount (n : ℕ) : ℕ := n.divisors.card

theorem sum_divisorCount (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, divisorCount n) =
      ∑ n ∈ Finset.Ioc 0 N, N / n := by
  simpa only [divisorCount, ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N

theorem harmonic_eq_sum_Ioc (N : ℕ) :
    harmonic N = ∑ n ∈ Finset.Ioc 0 N, (n : ℚ)⁻¹ := by
  rw [harmonic, Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun n : ℕ => (n : ℚ)⁻¹) 0 N (c := 1)]
  have hset : Finset.Ico 1 (N + 1) = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  simp only [zero_add, hset]

/-- The elementary mean bound needed by the revised good-degree selection.
This uses the exact divisor-pair identity, not a short-interval theorem. -/
theorem sum_divisorCount_le_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (divisorCount n : ℚ)) ≤ (N : ℚ) * harmonic N := by
  calc
    (∑ n ∈ Finset.Ioc 0 N, (divisorCount n : ℚ)) =
        ((∑ n ∈ Finset.Ioc 0 N, divisorCount n : ℕ) : ℚ) := by
      rw [Nat.cast_sum]
    _ = ((∑ n ∈ Finset.Ioc 0 N, N / n : ℕ) : ℚ) :=
      congrArg (fun m : ℕ => (m : ℚ)) (sum_divisorCount N)
    _ = ∑ n ∈ Finset.Ioc 0 N, ((N / n : ℕ) : ℚ) := by rw [Nat.cast_sum]
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (N : ℚ) / (n : ℚ) :=
      Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = (N : ℚ) * ∑ n ∈ Finset.Ioc 0 N, (n : ℚ)⁻¹ := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ = (N : ℚ) * harmonic N := by rw [harmonic_eq_sum_Ioc]

end Erdos345
