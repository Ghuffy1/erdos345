import Erdos345.ShiftedPrimeBound
import Erdos345.DivisorMean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos345

theorem shiftedPrimes_card_le_divisorCount {h : ℕ} (hh : 0 < h) :
    (shiftedPrimes h).card ≤ divisorCount h := by
  classical
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑(shiftedPrimes h) : Set ℕ) := by
    intro a ha b hb he
    have ha2 := (Finset.mem_filter.mp ha).2.1.two_le
    have hb2 := (Finset.mem_filter.mp hb).2.1.two_le
    dsimp only at he
    omega
  have hsub : (shiftedPrimes h).image (fun p => p - 1) ⊆ h.divisors := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hp).2.2, Nat.ne_of_gt hh⟩
  calc
    (shiftedPrimes h).card =
        ((shiftedPrimes h).image (fun p => p - 1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ h.divisors.card := Finset.card_le_card hsub
    _ = divisorCount h := rfl

theorem shiftedPrimeProduct_le {h : ℕ} (hh : 0 < h) :
    shiftedPrimeProduct h ≤ (h + 1) ^ divisorCount h := by
  have hprod : shiftedPrimeProduct h ≤ (h + 1) ^ (shiftedPrimes h).card := by
    calc
      shiftedPrimeProduct h ≤ ∏ _p ∈ shiftedPrimes h, (h + 1) := by
        change (∏ p ∈ shiftedPrimes h, p) ≤ ∏ _p ∈ shiftedPrimes h, (h + 1)
        apply Finset.prod_le_prod
        intro p hp
        have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        omega
      _ = (h + 1) ^ (shiftedPrimes h).card := by simp
  exact hprod.trans (Nat.pow_le_pow_right (by omega)
    (shiftedPrimes_card_le_divisorCount hh))

/-- A completely explicit natural-number envelope for the reduction modulus. -/
theorem reductionModulus_le_divisorEnvelope (k d : ℕ) (hd : d < k) :
    reductionModulus k d ≤
      (2 * k) ^ d * k ^ (∑ i ∈ Finset.range d, divisorCount (k - (i + 1))) := by
  have hpos :
      0 < ∏ i ∈ Finset.range d,
        2 * shiftedPrimeProduct (k - (i + 1)) * (k - (i + 1)) := by
    apply Finset.prod_pos
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact mul_pos (mul_pos (by decide) (shiftedPrimeProduct_pos _)) (by omega)
  calc
    reductionModulus k d ≤
        ∏ i ∈ Finset.range d,
          2 * shiftedPrimeProduct (k - (i + 1)) * (k - (i + 1)) :=
      Nat.le_of_dvd hpos (reductionModulus_dvd_shiftedPrimeBound k d hd)
    _ ≤ ∏ i ∈ Finset.range d, (2 * k) * k ^ divisorCount (k - (i + 1)) := by
      apply Finset.prod_le_prod
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hh : 0 < k - (i + 1) := by omega
      have hb : k - (i + 1) + 1 ≤ k := by omega
      have hD := (shiftedPrimeProduct_le hh).trans
        (Nat.pow_le_pow_left hb (divisorCount (k - (i + 1))))
      calc
        2 * shiftedPrimeProduct (k - (i + 1)) * (k - (i + 1)) =
            2 * (shiftedPrimeProduct (k - (i + 1)) * (k - (i + 1))) := by ring
        _ ≤ 2 * (k ^ divisorCount (k - (i + 1)) * k) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul hD (by omega))
        _ = (2 * k) * k ^ divisorCount (k - (i + 1)) := by ring
    _ = (2 * k) ^ d * k ^ (∑ i ∈ Finset.range d, divisorCount (k - (i + 1))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

theorem log_reductionModulus_le (k d : ℕ) (hd : d < k) :
    Real.log (reductionModulus k d : ℝ) ≤
      (d : ℝ) * Real.log ((2 * k : ℕ) : ℝ) +
        (∑ i ∈ Finset.range d, divisorCount (k - (i + 1)) : ℕ) * Real.log (k : ℝ) := by
  have hk : 0 < k := by omega
  have hg : 0 < (reductionModulus k d : ℝ) := by
    exact_mod_cast reductionModulus_pos hd
  have hbase : ((2 * k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos (by decide) hk)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have henv :
      (reductionModulus k d : ℝ) ≤
        ((2 * k : ℕ) : ℝ) ^ d *
          (k : ℝ) ^ (∑ i ∈ Finset.range d, divisorCount (k - (i + 1))) := by
    exact_mod_cast reductionModulus_le_divisorEnvelope k d hd
  have hlog := Real.log_le_log hg henv
  rw [Real.log_mul (pow_ne_zero _ hbase) (pow_ne_zero _ hk'),
    Real.log_pow, Real.log_pow] at hlog
  exact hlog

end Erdos345
