import Erdos345.FlatDenominatorNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos345

open Finset

theorem log_regularizedNorm_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    Real.log (regularizedCyclotomicNorm (Icc 1 N) m (p ^ (k + 1))) ≤
      ((p ^ (k + 1)).totient : ℝ) * (rootSlots N w (p ^ (k + 1)) : ℝ) * Real.log N +
        ((k + 1) * weightMass N w : ℕ) * Real.log p := by
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hbound := (regularizedCyclotomicNorm_mono (Icc 1 N) m (rootSlots N w) hS
    (p ^ (k + 1)) ht hm).trans (flat_regularizedNorm_le hw p k hp ht)
  have hpos : 0 < regularizedCyclotomicNorm (Icc 1 N) m (p ^ (k + 1)) :=
    lt_of_lt_of_le zero_lt_one (regularizedCyclotomicNorm_ge_one (Icc 1 N) m hS
      (p ^ (k + 1)) (pow_pos hp.pos _))
  have hN : (N : ℝ) ≠ 0 := by
    have ht' := mem_Icc.mp ht
    have : 0 < N := lt_of_lt_of_le (pow_pos hp.pos _) ht'.2
    exact_mod_cast Nat.ne_of_gt this
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hN)) (pow_ne_zero _ hp0),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  nlinarith [hlog]

theorem primePower_le_twice_totient (p k : ℕ) (hp : p.Prime) :
    p ^ (k + 1) ≤ 2 * (p ^ (k + 1)).totient := by
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have hp' : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
  have hm := Nat.mul_le_mul_left (p ^ k) hp'
  nlinarith

/-- Scaled logarithmic denominator bound with the prime-power conductor
visible. It uses the proved cancellation inequality and exact factor norms. -/
theorem scaled_log_regularizedNorm_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    (p ^ (k + 1) : ℕ) * Real.log (regularizedCyclotomicNorm (Icc 1 N) m (p ^ (k + 1))) ≤
      ((p ^ (k + 1)).totient : ℝ) * (weightMass N w : ℝ) *
        (Real.log N + 2 * Real.log (p ^ (k + 1) : ℕ)) := by
  have hb := mul_le_mul_of_nonneg_left (log_regularizedNorm_le hw m hm p k hp ht)
    (Nat.cast_nonneg (p ^ (k + 1)))
  have hslot : (p ^ (k + 1) : ℕ) * (rootSlots N w (p ^ (k + 1)) : ℝ) ≤ weightMass N w := by
    exact_mod_cast rootSlots_mul_le_mass hw (p ^ (k + 1))
  have hratio : (p ^ (k + 1) : ℕ) ≤ (2 : ℝ) * (p ^ (k + 1)).totient := by
    exact_mod_cast primePower_le_twice_totient p k hp
  have hN := Real.log_natCast_nonneg N
  have hpLog := Real.log_natCast_nonneg p
  have hterm1 := mul_le_mul_of_nonneg_right hslot
    (mul_nonneg (Nat.cast_nonneg ((p ^ (k + 1)).totient)) hN)
  have hterm2 := mul_le_mul_of_nonneg_right hratio
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg (k + 1)) (Nat.cast_nonneg (weightMass N w))) hpLog)
  have htLog : Real.log (p ^ (k + 1) : ℕ) = ((k + 1 : ℕ) : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [htLog]
  simp only [Nat.cast_mul] at hb
  nlinarith [hb, hterm1, hterm2]

theorem scaled_log_regularizedNorm_le_three
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    (p ^ (k + 1) : ℕ) * Real.log (regularizedCyclotomicNorm (Icc 1 N) m (p ^ (k + 1))) ≤
      3 * ((p ^ (k + 1)).totient : ℝ) * (weightMass N w : ℝ) * Real.log N := by
  have hb := scaled_log_regularizedNorm_le hw m hm p k hp ht
  have hlog : Real.log (p ^ (k + 1) : ℕ) ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast pow_pos hp.pos (k + 1))
    exact_mod_cast (mem_Icc.mp ht).2
  have hmul := mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (Nat.cast_nonneg ((p ^ (k + 1)).totient)) (Nat.cast_nonneg (weightMass N w)))
  nlinarith [hb, hmul]

end Erdos345
