import Erdos345.PrimeLogRatio
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos345

theorem sum_abs_sine_zero_bin (P : Finset ℕ) (A v : ℕ) (t : ℝ)
    (hA : 2 ≤ A) (ht : 1 < t) (hprime : ∀ p ∈ P, p.Prime)
    (hbound : ∀ p ∈ P, p ≤ A) (hsmall : ∀ p ∈ P, (p : ℝ) < t / 2)
    (hbin : ∀ p ∈ P, primePhaseBin (t / 2) p = 0) :
    (∑ p ∈ P, |scaledSineBlock p v t|) ≤
      (4 * (A : ℝ) * Real.log t / Real.log (A : ℝ)) * v := by
  have hp := sum_prime_weights_of_phaseBin P A (t / 2) 0 hA (by linarith)
    hprime hbound hsmall hbin
  rw [show 2 * (t / 2) = t by ring] at hp
  have hs : (∑ p ∈ P, |scaledSineBlock p v t|) ≤ (∑ p ∈ P, (p : ℝ)) * v := by
    calc
      _ ≤ ∑ p ∈ P, ((p * v : ℕ) : ℝ) := Finset.sum_le_sum (fun p _ => scaledSineBlock_abs_le p v t)
      _ = _ := by push_cast; rw [Finset.sum_mul]
  exact hs.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg v))

theorem sum_abs_sine_positive_bin (P : Finset ℕ) (A v j : ℕ) (t : ℝ)
    (hA : 2 ≤ A) (hj : 0 < j) (ht : 1 < t) (hprime : ∀ p ∈ P, p.Prime)
    (hbound : ∀ p ∈ P, p ≤ A) (hsmall : ∀ p ∈ P, (p : ℝ) < t / 2)
    (hbin : ∀ p ∈ P, primePhaseBin (t / 2) p = j) :
    (∑ p ∈ P, |scaledSineBlock p v t|) ≤
      (4 * (A : ℝ) * Real.log t / Real.log (A : ℝ)) / (2 * (j : ℝ)) := by
  have hp := sum_prime_weights_of_phaseBin P A (t / 2) j hA (by linarith)
    hprime hbound hsmall hbin
  rw [show 2 * (t / 2) = t by ring] at hp
  have hs : (∑ p ∈ P, |scaledSineBlock p v t|) ≤ (∑ p ∈ P, (p : ℝ)) / (2 * (j : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ P, (p : ℝ) / (2 * (j : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hP
        have hb := scaledSineBlock_abs_le_phaseBin p v (hprime p hP).pos t (by rw [hbin p hP]; exact hj)
        simpa only [hbin p hP] using hb
      _ = _ := by rw [Finset.sum_div]
  exact hs.trans (div_le_div_of_nonneg_right hp (by positivity))

end Erdos345
