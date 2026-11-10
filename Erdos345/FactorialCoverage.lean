import Erdos345.PrimaryExponentBound
import Mathlib.Data.Nat.Factorial.BigOperators

namespace Erdos345

open Finset

/-- A coarse factorial coverage estimate, proved without asymptotics. -/
theorem power_dvd_factorial_of_mul_le (p e M : ℕ) (hp : 0 < p) (hpe : p * e ≤ M) :
    p ^ e ∣ M.factorial := by
  have hfirst : p ^ e ∣ p.factorial ^ e :=
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hp le_rfl) e
  have hsecond : p.factorial ^ e ∣ (p * e).factorial := by
    simpa only [prod_const, card_range, sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm] using
      Nat.prod_factorial_dvd_factorial_sum (range e) (fun _ => p)
  exact hfirst.trans (hsecond.trans (Nat.factorial_dvd_factorial hpe))

theorem prime_scaled_exponent_bound (p e : ℕ) (hp : p.Prime)
    (A B T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hpT : (p : ℝ) ≤ T)
    (he : (e : ℝ) ≤ A * T / ((p - 1 : ℕ) : ℝ) + B) :
    (p : ℝ) * e ≤ (2 * A + B) * T := by
  have hb : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by have := hp.two_le; omega : 0 < p - 1)
  have hp2 : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by have := hp.two_le; omega : p ≤ 2 * (p - 1))
  have hratio : (p : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 2 :=
    (div_le_iff₀ hb).mpr hp2
  calc
    (p : ℝ) * e ≤ p * (A * T / ((p - 1 : ℕ) : ℝ) + B) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg p)
    _ = ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) * (A * T) + p * B := by ring
    _ ≤ 2 * (A * T) + T * B := add_le_add
      (mul_le_mul_of_nonneg_right hratio (mul_nonneg hA hT))
      (mul_le_mul_of_nonneg_right hpT hB)
    _ = (2 * A + B) * T := by ring

def conductorCoefficient (N k : ℕ) : ℝ :=
  2 * (((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 5)) +
    ((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 k : ℝ) + 1)

theorem conductorCoefficient_ge_one (N k : ℕ) : 1 ≤ conductorCoefficient N k := by
  have hN : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ Nat.log 2 k := Nat.cast_nonneg _
  unfold conductorCoefficient
  nlinarith [sq_nonneg (Nat.log 2 N : ℝ), mul_nonneg hN hk]

/-- Replace the prime-dependent logarithms by uniform base-two bounds. -/
theorem primary_uniform_exponent_bound (S : Finset ℕ) (m : ℕ → ℕ)
    (p e k N : ℕ) (hp : p.Prime)
    (hmax : ∀ n ∈ S, n ≤ N) (hm : ∀ n ∈ S, m n ≤ k)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n)
    (T : ℝ) (hT : 0 ≤ T) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T) :
    (e : ℝ) ≤
      (((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 5) * T) /
        ((p - 1 : ℕ) : ℝ) +
      ((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 k : ℝ) + 1) := by
  have hN : (Nat.log p N : ℝ) ≤ Nat.log 2 N := by
    exact_mod_cast Nat.log_anti_left (by decide : 1 < 2) hp.two_le
  have hk : (Nat.log p k : ℝ) ≤ Nat.log 2 k := by
    exact_mod_cast Nat.log_anti_left (by decide : 1 < 2) hp.two_le
  have hA : ((Nat.log p N : ℝ) + 1) * ((Nat.log p N : ℝ) + 5) ≤
      ((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 5) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hB : ((Nat.log p N : ℝ) + 1) * ((Nat.log p k : ℝ) + 1) ≤
      ((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 k : ℝ) + 1) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  exact (primary_exponent_bound S m p e k N hp hmax hm hglobal T hT hroot hbound).trans
    (add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA hT)
      (Nat.cast_nonneg (p - 1))) hB)

end Erdos345
