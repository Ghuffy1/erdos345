import Erdos345.ScalingDifference
import Mathlib.Data.Nat.GCD.Basic

namespace Erdos345

/-- Absolute integer difference, so the definition also makes sense when j>k. -/
def fixedDifference (k j a : ℕ) : ℕ :=
  Int.natAbs ((a : ℤ) ^ k - (a : ℤ) ^ j)

/-- A finite fixed divisor. The selected sample range contains at least k+1
points, enough to determine the degree-k polynomial when j≤k. -/
def fixedDifferenceDivisor (k j : ℕ) : ℕ :=
  (Finset.range (k + 3)).gcd (fixedDifference k j)

/-- The finite definition is the genuine fixed divisor on all natural inputs. -/
theorem dvd_fixedDifferenceDivisor_iff (q k j : ℕ) (hjk : j ≤ k) :
    q ∣ fixedDifferenceDivisor k j ↔ ∀ a : ℕ, q ∣ fixedDifference k j a := by
  constructor
  · intro h
    have hsample : ∀ a : ℕ, a ≤ k → (a : ZMod q) ^ k - (a : ZMod q) ^ j = 0 := by
      intro a ha
      have hd : q ∣ fixedDifference k j a :=
        (Finset.dvd_gcd_iff.mp h) a (Finset.mem_range.mpr (by omega))
      have hz : (q : ℤ) ∣ (a : ℤ) ^ k - (a : ℤ) ^ j :=
        Int.natCast_dvd.mpr hd
      have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) ^ k - (a : ℤ) ^ j) q).mpr hz
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using hc
    let f : ℕ → ZMod q := fun a => (a : ZMod q) ^ k - (a : ZMod q) ^ j
    have hcoeff : ∀ s : ℕ, iteratedDifference s f 0 = 0 := by
      intro s
      by_cases hs : s ≤ k
      · apply iteratedDifference_zero_of_prefix
        intro i hi
        simpa only [f, Nat.zero_add] using hsample i (hi.trans hs)
      · dsimp only [f]
        rw [iteratedDifference_sub, iteratedDifference_power_zero, iteratedDifference_power_zero]
        simp only [powerCoefficient_eq_zero (by omega : k < s),
          powerCoefficient_eq_zero (by omega : j < s), Nat.cast_zero, sub_self]
    have hvalue : ∀ a : ℕ, f a = 0 := by
      intro a
      rw [← newton_forward_formula f a]
      apply Finset.sum_eq_zero
      intro s _
      dsimp only
      rw [hcoeff, zero_mul]
    intro a
    apply Int.natCast_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) ^ k - (a : ℤ) ^ j) q).mp
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using hvalue a
  · intro h
    exact Finset.dvd_gcd_iff.mpr (fun a _ => h a)

theorem fixedDifferenceDivisor_pos {k j : ℕ} (hjk : j < k) :
    0 < fixedDifferenceDivisor k j := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hd : fixedDifferenceDivisor k j ∣ fixedDifference k j 2 :=
    (dvd_fixedDifferenceDivisor_iff _ _ _ hjk.le).mp dvd_rfl 2
  rw [hz] at hd
  have heq : fixedDifference k j 2 = 0 := (zero_dvd_iff.mp hd)
  have hpow : (2 : ℤ) ^ j < (2 : ℤ) ^ k := pow_lt_pow_right₀ (by decide) hjk
  have hne : (2 : ℤ) ^ k - (2 : ℤ) ^ j ≠ 0 := sub_ne_zero.mpr hpow.ne'
  exact hne (Int.natAbs_eq_zero.mp heq)

theorem reduction_quotient_dvd_fixedDifference {q k j : ℕ}
    (hq : 0 < q) (h : q ∣ reductionModulus k j) (a : ℕ) :
    q / Nat.gcd q (powerCoefficient k j) ∣ fixedDifference k j a := by
  have hi := reductionModulus_scaling_difference h a
  have hn : q ∣ powerCoefficient k j * fixedDifference k j a := by
    have ha := Int.natCast_dvd.mp hi
    have he : (a : ℤ) ^ j - (a : ℤ) ^ k = -((a : ℤ) ^ k - (a : ℤ) ^ j) := by ring
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, he, Int.natAbs_neg,
      fixedDifference] using ha
  apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q (powerCoefficient k j))
    (Nat.gcd_pos_of_pos_left _ hq)).mpr
  exact dvd_gcd_mul_of_dvd_mul hn

theorem reduction_quotient_dvd_fixedDivisor {q k j : ℕ}
    (hq : 0 < q) (h : q ∣ reductionModulus k j) :
    q / Nat.gcd q (powerCoefficient k j) ∣ fixedDifferenceDivisor k j := by
  apply Finset.dvd_gcd_iff.mpr
  intro a _
  exact reduction_quotient_dvd_fixedDifference hq h a

theorem reductionModulus_pos {k d : ℕ} (hd : d < k) :
    0 < reductionModulus k d := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hdiv := (dvd_reductionModulus_iff _ _ _).mp
    (dvd_rfl : reductionModulus k d ∣ reductionModulus k d) k hd
  exact Nat.factorial_ne_zero k (by
    simpa [hzero, powerCoefficient, Nat.stirlingSecond_self] using hdiv)

/-- The all-prime telescoping product bound for the exact reduction modulus. -/
theorem reductionModulus_dvd_fixedProduct (k d : ℕ) (hd : d < k) :
    reductionModulus k d ∣ ∏ i ∈ Finset.range d, fixedDifferenceDivisor k (i + 1) := by
  revert hd
  induction d with
  | zero =>
    intro hk
    simp [reductionModulus_zero (by omega : 0 < k)]
  | succ d ih =>
    intro hdk
    have ihd := ih (by omega : d < k)
    let q := reductionModulus k (d + 1)
    have hq : 0 < q := reductionModulus_pos hdk
    have hquot := reduction_quotient_dvd_fixedDivisor hq
      (dvd_rfl : q ∣ reductionModulus k (d + 1))
    have hgcd : Nat.gcd q (powerCoefficient k (d + 1)) = reductionModulus k d := by
      rw [reductionModulus_step k d, Nat.gcd_comm]
    rw [hgcd] at hquot
    have hdiv : reductionModulus k d ∣ q :=
      reductionModulus_mono_dvd k (Nat.le_succ d)
    have hmul := Nat.mul_dvd_mul ihd hquot
    rw [Nat.mul_div_cancel' hdiv] at hmul
    simpa only [Finset.prod_range_succ] using hmul

end Erdos345
