import Erdos345.UnitFactorCancellation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

namespace Erdos345

open Finset Polynomial

theorem cyclotomic_eval_one_isUnit_primePower
    (r e n : ℕ) (hr : r.Prime) (hn : n ≠ 1)
    (hnot : ∀ a : ℕ, n ≠ r ^ (a + 1)) :
    IsUnit (((cyclotomic n ℤ).eval 1 : ℤ) : ZMod (r ^ e)) := by
  classical
  by_cases hex : ∃ p a : ℕ, p.Prime ∧ n = p ^ (a + 1)
  · obtain ⟨p, a, hp, hnp⟩ := hex
    have hpr : p ≠ r := by
      intro h
      subst p
      exact hnot a hnp
    let : Fact p.Prime := ⟨hp⟩
    rw [hnp, eval_one_cyclotomic_prime_pow]
    simp only [Int.cast_natCast]
    apply (ZMod.isUnit_iff_coprime p (r ^ e)).mpr
    exact ((Nat.coprime_primes hp hr).mpr hpr).pow_right e
  · have hfree : ∀ {p : ℕ}, p.Prime → ∀ a : ℕ, p ^ a ≠ n := by
      intro p hp a
      cases a with
      | zero => simpa only [pow_zero, ne_eq, eq_comm] using hn
      | succ a =>
        intro h
        exact hex ⟨p, a, hp, h.symm⟩
    rw [eval_one_cyclotomic_not_prime_pow hfree]
    simp

noncomputable def cyclotomicProduct (S : Finset ℕ) (m : ℕ → ℕ) : ℤ[X] :=
  ∏ n ∈ S, (cyclotomic n ℤ) ^ m n

theorem cyclotomicProduct_eval_one_isUnit (S : Finset ℕ) (m : ℕ → ℕ)
    (r e : ℕ) (hr : r.Prime)
    (hS : ∀ n ∈ S, n ≠ 1 ∧ ∀ a : ℕ, n ≠ r ^ (a + 1)) :
    IsUnit (((cyclotomicProduct S m).eval 1 : ℤ) : ZMod (r ^ e)) := by
  rw [cyclotomicProduct, eval_prod, Int.cast_prod]
  apply IsUnit.prod_iff.mpr
  intro n hn
  rw [eval_pow, Int.cast_pow]
  exact (cyclotomic_eval_one_isUnit_primePower r e n hr (hS n hn).1 (hS n hn).2).pow (m n)

/-- Factors of orders other than one and r-powers may be removed from the
original power-sequence annihilator modulo r^e. -/
theorem remove_nonprimary_cyclotomic_factors (P : ℤ[X]) (S : Finset ℕ) (m : ℕ → ℕ)
    (r e k : ℕ) (hr : r.Prime)
    (hS : ∀ n ∈ S, n ≠ 1 ∧ ∀ a : ℕ, n ≠ r ^ (a + 1))
    (han : ∀ n, ((r ^ e : ℕ) : ℤ) ∣
      shiftAction (P * cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    ∀ n, ((r ^ e : ℕ) : ℤ) ∣ shiftAction P (fun j : ℕ => (j : ℤ) ^ k) n :=
  remove_unit_factor_from_power_annihilator P (cyclotomicProduct S m) (r ^ e) k
    (cyclotomicProduct_eval_one_isUnit S m r e hr hS) han

end Erdos345
