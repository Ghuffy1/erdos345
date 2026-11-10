import Erdos345.FiniteObstruction
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

namespace Erdos345

theorem baseSum_twice (H : ℕ) : baseSum H * 2 = (H + 1) * H := by
  simpa [baseSum] using Finset.sum_range_id_mul_two (H + 1)

theorem baseSum_sqrt_gap {Q : ℕ} (hQ : 9 ≤ Q) :
    baseSum (Nat.sqrt Q) + 1 < Q := by
  have hH : 3 ≤ Nat.sqrt Q := Nat.le_sqrt.mpr (by simpa using hQ)
  have hsq := Nat.sqrt_le Q
  have hsum := baseSum_twice (Nat.sqrt Q)
  have hmul := Nat.mul_le_mul_left (Nat.sqrt Q) hH
  nlinarith

theorem sqrt_succ_pow_ge {Q k : ℕ} (hk : 2 ≤ k) :
    Q ≤ (Nat.sqrt Q + 1) ^ k := by
  have hroot : Q < (Nat.sqrt Q + 1) ^ 2 := Nat.lt_succ_sqrt' Q
  have hpow : (Nat.sqrt Q + 1) ^ 2 ≤ (Nat.sqrt Q + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) hk
  exact (Nat.le_of_lt hroot).trans hpow

/-- The arithmetic lower-bound construction in the candidate proof.

This constructs a missing integer immediately below the first excluded power.
The analytic theorem asserting sufficiently many eligible primes is a separate,
still-unformalized input.
-/
theorem exists_exception_from_shifted_primes (P : Finset ℕ) (t : ℕ)
    (ht : 1 ≤ t) (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ∀ p ∈ P, p - 1 ∣ t) (hsize : 9 ≤ ∏ p ∈ P, p) :
    ∃ m : ℕ,
      (Nat.sqrt (∏ p ∈ P, p) + 1) ^ (t + 1) - (∏ p ∈ P, p) ≤ m ∧
      m < (Nat.sqrt (∏ p ∈ P, p) + 1) ^ (t + 1) ∧
      ¬ represented (t + 1) m := by
  apply exists_exception_from_residue
  · omega
  · exact sqrt_succ_pow_ge (by omega)
  · exact baseSum_sqrt_gap hsize
  · intro n
    exact shifted_power_mod_prime_product P t n hP hdiv

theorem threshold_lower_bound_from_shifted_primes
    (P : Finset ℕ) (t a : ℕ) (ht : 1 ≤ t)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p - 1 ∣ t)
    (hsize : 9 ≤ ∏ p ∈ P, p)
    (ha : a ∈ thresholds (kthPowers (t + 1))) :
    (Nat.sqrt (∏ p ∈ P, p) + 1) ^ (t + 1) - (∏ p ∈ P, p) < a := by
  obtain ⟨m, hlo, _, hnot⟩ :=
    exists_exception_from_shifted_primes P t ht hP hdiv hsize
  exact hlo.trans_lt (exception_lt_threshold (by omega) hnot ha)

end Erdos345
