import Erdos345.DilationValuations
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace Erdos345

open Finset

theorem five_period_two_power (a : ℕ) :
    Nat.ModEq (2 ^ a) (5 ^ (2 ^ (a - 2))) 1 := by
  by_cases ha : a < 2
  · interval_cases a <;> decide
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ a by omega)
    have hpow := pow_orderOf_eq_one (5 : ZMod (2 ^ (b + 2)))
    rw [ZMod.orderOf_five] at hpow
    have hcast : ((5 ^ (2 ^ b) : ℕ) : ZMod (2 ^ (b + 2))) = (1 : ℕ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow
    simpa only [Nat.add_comm 2 b, Nat.add_sub_cancel] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

def twoPowerDilationPeriod (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n - 2)

theorem twoPowerDilationPeriod_pos (n : ℕ) : 0 < twoPowerDilationPeriod n :=
  Nat.pow_pos (by decide)

theorem twoPowerDilationPeriod_period (a : ℕ) :
    Nat.ModEq (2 ^ a) (5 ^ twoPowerDilationPeriod (2 ^ a)) 1 := by
  simpa only [twoPowerDilationPeriod, Nat.log_pow (by decide : 1 < (2 : ℕ))] using
    five_period_two_power a

/-- The full two-adic dilation estimate, for any finite collection of two-power
root orders. The recurrence and multiplicity hypotheses are explicit. -/
theorem twoAdic_cyclotomic_multiplicity_bound
    (S : Finset ℕ) (m : ℕ → ℕ) (e k : ℕ)
    (hS : ∀ n ∈ S, ∃ a : ℕ, n = 2 ^ a)
    (hm : ∀ n ∈ S, m n ≤ k)
    (hpower : ∀ n, ((2 ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    e ≤ ∑ n ∈ S, ((2 + (Nat.log 2 n - 2)) * m n + valuationWindow 2 k (m n)) := by
  have hp := primePower_le_dilation_valuation_sum S m twoPowerDilationPeriod
    5 2 e k Nat.prime_two (by decide)
    (fun n hn => by obtain ⟨a, rfl⟩ := hS n hn; exact Nat.pow_pos (by decide))
    (fun n _ => twoPowerDilationPeriod_pos n) hm
    (fun n hn => by obtain ⟨a, rfl⟩ := hS n hn; exact twoPowerDilationPeriod_period a)
    hpower
  calc
    e ≤ ∑ n ∈ S, ∑ j ∈ range (m n),
        (dilationDifference 5 k j (twoPowerDilationPeriod n)).factorization 2 := hp
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      calc
        (∑ j ∈ range (m n),
            (dilationDifference 5 k j (twoPowerDilationPeriod n)).factorization 2) =
            ∑ j ∈ range (m n), (2 + (Nat.log 2 n - 2) + (k - j).factorization 2) := by
          apply sum_congr rfl
          intro j hj
          rw [dilationDifference_five_factorization
            (lt_of_lt_of_le (mem_range.mp hj) (hm n hn)) (twoPowerDilationPeriod_pos n),
            twoPowerDilationPeriod]
          simp only [Nat.factorization_pow, Finsupp.nsmul_apply,
            Nat.prime_two.factorization_self, nsmul_eq_mul, mul_one, Nat.cast_id]
          ring
        _ = _ := by
          rw [sum_add_distrib]
          simp only [sum_const, card_range, smul_eq_mul, valuationWindow]
          ring

theorem twoAdic_cyclotomic_multiplicity_log_bound
    (S : Finset ℕ) (m : ℕ → ℕ) (e k : ℕ)
    (hS : ∀ n ∈ S, ∃ a : ℕ, n = 2 ^ a)
    (hm : ∀ n ∈ S, m n ≤ k)
    (hpower : ∀ n, ((2 ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    e ≤ ∑ n ∈ S, ((3 + (Nat.log 2 n - 2)) * m n + Nat.log 2 k) := by
  apply (twoAdic_cyclotomic_multiplicity_bound S m e k hS hm hpower).trans
  apply sum_le_sum
  intro n hn
  have hw := valuationWindow_scaled_le 2 k (m n) Nat.prime_two (hm n hn)
  norm_num at hw
  nlinarith

end Erdos345
