import Erdos345.FactorialCoverage
import Erdos345.MinimalReduction

namespace Erdos345

open Finset Polynomial

/-- A finite conductor theorem. Small primes are covered by a factorial;
large primes leave only the root-one factor in the primary annihilator. -/
theorem conductor_divisibility_of_heights (S : Finset ℕ) (m : ℕ → ℕ)
    (q k N M : ℕ) (h1 : 1 ∈ S) (hmax : ∀ n ∈ S, n ≤ N)
    (hm : ∀ n ∈ S, m n ≤ k)
    (hglobal : ∀ n, (q : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n)
    (T : ℝ) (hT : 0 ≤ T) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ p : ℕ, p.Prime →
      ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T)
    (hbudget : conductorCoefficient N k * T ≤ M) :
    q ∣ reductionModulus k M := by
  have hTM : T ≤ (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (conductorCoefficient_ge_one N k) hT
    have h' : T ≤ conductorCoefficient N k * T := by simpa only [one_mul] using h
    exact h'.trans hbudget
  have hrootM : m 1 ≤ M := by exact_mod_cast hroot.trans hTM
  apply (Nat.dvd_iff_prime_pow_dvd_dvd (reductionModulus k M) q).mpr
  intro p e hp hpeq
  have hpeqZ : ((p ^ e : ℕ) : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpeq
  have hpe : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n :=
    fun n => hpeqZ.trans (hglobal n)
  by_cases hpT : (p : ℝ) ≤ T
  · have he := primary_uniform_exponent_bound S m p e k N hp hmax hm hpe
      T hT hroot (hbound p hp)
    have hscaled := prime_scaled_exponent_bound p e hp
      (((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 5))
      (((Nat.log 2 N : ℝ) + 1) * ((Nat.log 2 k : ℝ) + 1)) T
      (by positivity) (by positivity) hT hpT he
    have hpeM : p * e ≤ M := by
      have h : (p : ℝ) * e ≤ (M : ℝ) := hscaled.trans hbudget
      exact_mod_cast h
    exact (power_dvd_factorial_of_mul_le p e M hp.pos hpeM).trans
      (factorial_dvd_reductionModulus k M)
  · have hlarge := large_prime_power_reduction S m p e k hp h1 T
      (lt_of_not_ge hpT) (hbound p hp) hpe
    by_cases hm0 : m 1 = 0
    · rw [hlarge.1 hm0]
      exact one_dvd _
    · exact (hlarge.2 (Nat.pos_of_ne_zero hm0)).trans
        (reductionModulus_mono_dvd k ((Nat.sub_le (m 1) 1).trans hrootM))

theorem conductor_minimal_degree_bound (S : Finset ℕ) (m : ℕ → ℕ)
    (q k N M : ℕ) (h1 : 1 ∈ S) (hmax : ∀ n ∈ S, n ≤ N)
    (hm : ∀ n ∈ S, m n ≤ k)
    (hglobal : ∀ n, (q : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n)
    (T : ℝ) (hT : 0 ≤ T) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ p : ℕ, p.Prime →
      ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T)
    (hbudget : conductorCoefficient N k * T ≤ M) :
    minimalReductionDegree q k ≤ M :=
  minimalReductionDegree_le
    (conductor_divisibility_of_heights S m q k N M h1 hmax hm hglobal T hT hroot hbound hbudget)

/-- The same conductor theorem for a rational approximation error with
an actual minimal recurrence and an integral numerator congruence. -/
theorem rational_error_conductor_divisibility (S : Finset ℕ) (m : ℕ → ℕ)
    (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X]) (q u k N M : ℕ)
    (hq : 0 < q) (hu : u.Coprime q)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hphase : ∀ n : ℕ, f n + (g n : ℚ) = P.eval (n : ℚ))
    (hscale : ∀ n, (z n : ℚ) = (q : ℚ) * f n)
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (h1 : 1 ∈ S) (hmax : ∀ n ∈ S, n ≤ N) (hm : ∀ n ∈ S, m n ≤ k)
    (T : ℝ) (hT : 0 ≤ T) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ p : ℕ, p.Prime →
      ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T)
    (hbudget : conductorCoefficient N k * T ≤ M) :
    q ∣ reductionModulus k M :=
  conductor_divisibility_of_heights S m q k N M h1 hmax hm
    (rational_error_annihilator_mod_power S m f g z P q u k hq hu hminimal hphase hscale hPmod)
    T hT hroot hbound hbudget

end Erdos345
