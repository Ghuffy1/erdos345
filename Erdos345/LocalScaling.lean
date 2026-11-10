import Erdos345.OddPrimeDilation
import Erdos345.TwoAdicDilation

namespace Erdos345

open Finset

/-- A uniform local-scaling estimate at every prime. The support consists of
one and prime-power root orders; the exponent of every factor is at most k.
No characteristic factorization or primitive-root existence is assumed. -/
theorem local_scaling_multiplicity_bound
    (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ) (hp : p.Prime)
    (hS : ∀ n ∈ S, ∃ a : ℕ, n = p ^ a) (hm : ∀ n ∈ S, m n ≤ k)
    (hpower : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    (p - 1) * e ≤ ∑ n ∈ S, if n = 1 then
      3 * m n + (p - 1) * (Nat.log p k + 1) else
      (p - 1) * ((Nat.log p n + 2) * m n + Nat.log p k + 1) := by
  by_cases hp2 : p = 2
  · subst p
    simp only [Nat.reduceSub, one_mul]
    apply (twoAdic_cyclotomic_multiplicity_log_bound S m e k hS hm hpower).trans
    apply sum_le_sum
    intro n hn
    by_cases h1 : n = 1
    · rw [ite_eq_left h1, h1, Nat.log_one_right]
      simp only [Nat.zero_sub, add_zero]
      omega
    · rw [ite_eq_right h1]
      obtain ⟨a, ha⟩ := hS n hn
      have hlog : Nat.log 2 n = a := by rw [ha, Nat.log_pow (by decide : 1 < (2 : ℕ))]
      rw [hlog]
      have hc : 3 + (a - 2) ≤ a + 2 := by
        have ha1 : 1 ≤ a := by
          by_contra h
          have ha0 : a = 0 := by omega
          simp only [ha0, pow_zero] at ha
          exact h1 ha
        omega
      have hmul := Nat.mul_le_mul_right (m n) hc
      omega
  · apply (oddPrime_cyclotomic_multiplicity_log_bound S m p e k hp hp2 hS hm hpower).trans
    apply sum_le_sum
    intro n hn
    by_cases h1 : n = 1
    · simp only [ite_eq_left h1]
      omega
    · simp only [ite_eq_right h1]
      have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
      have hc : (p - 1) * Nat.log p n + 1 ≤ (p - 1) * (Nat.log p n + 2) := by
        nlinarith
      have hmul := Nat.mul_le_mul_right (m n) hc
      have htail := Nat.mul_le_mul_left (p - 1) (Nat.le_succ (Nat.log p k))
      calc
        ((p - 1) * Nat.log p n + 1) * m n + (p - 1) * Nat.log p k ≤
            ((p - 1) * (Nat.log p n + 2)) * m n + (p - 1) * (Nat.log p k + 1) :=
          Nat.add_le_add hmul htail
        _ = _ := by ring

end Erdos345
