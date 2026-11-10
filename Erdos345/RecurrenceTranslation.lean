import Erdos345.IntegerRecurrenceEnergy

namespace Erdos345

open Finset Polynomial

theorem shiftAction_translate_general {R : Type*} [CommRing R]
    (P : R[X]) (f : ℕ → R) (a n : ℕ) :
    shiftAction P (fun j => f (a + j)) n = shiftAction P f (a + n) := by
  simp only [shiftAction_sum, Nat.add_assoc]

theorem recurrence_zero_of_zero_tail {K : Type*} [Field K]
    (P : K[X]) (hP : P.coeff 0 ≠ 0) (f : ℕ → K)
    (hrec : shiftAction P f = 0) (a : ℕ) (htail : ∀ n, a ≤ n → f n = 0) : f = 0 := by
  have hall : ∀ d n : ℕ, a - n = d → f n = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n hdn
      by_cases han : a ≤ n
      · exact htail n han
      have hrow := congrFun hrec n
      rw [shiftAction_sum, sum_range_succ'] at hrow
      have hrest : (∑ j ∈ range P.natDegree, P.coeff (j + 1) * f (n + (j + 1))) = 0 := by
        apply sum_eq_zero
        intro j _
        have hsmall : a - (n + (j + 1)) < d := by omega
        rw [ih _ hsmall _ rfl, mul_zero]
      have hzero : P.coeff 0 * f n = 0 := by
        simpa only [hrest, Nat.add_zero, zero_add, add_zero, Pi.zero_apply] using hrow
      exact (mul_eq_zero.mp hzero).resolve_left hP
  exact funext (fun n => hall (a - n) n rfl)

/-- A recurrence with nonzero constant term has the same annihilators
after translating the interval. The proof propagates a zero tail back. -/
theorem sequenceAnnihilator_translate {K : Type*} [Field K]
    (P : K[X]) (hP : P.coeff 0 ≠ 0) (f : ℕ → K)
    (hrec : shiftAction P f = 0) (a : ℕ) :
    sequenceAnnihilator (fun n => f (a + n)) = sequenceAnnihilator f := by
  ext Q
  change shiftAction Q (fun n => f (a + n)) = 0 ↔ shiftAction Q f = 0
  constructor
  · intro hQ
    have hg : shiftAction P (shiftAction Q f) = 0 := by
      rw [← shiftAction_mul, mul_comm P Q, shiftAction_mul, hrec, shiftAction_zero_sequence]
    apply recurrence_zero_of_zero_tail P hP (shiftAction Q f) hg a
    intro n hn
    have h := congrFun hQ (n - a)
    rw [shiftAction_translate_general, Nat.add_sub_of_le hn] at h
    exact h
  · intro hQ
    funext n
    rw [shiftAction_translate_general]
    exact congrFun hQ (a + n)

theorem minimalAnnihilator_translate {K : Type*} [Field K]
    (P : K[X]) (hP : P.coeff 0 ≠ 0) (f : ℕ → K)
    (hrec : shiftAction P f = 0) (a : ℕ) :
    minimalAnnihilator (fun n => f (a + n)) = minimalAnnihilator f := by
  classical
  exact congrArg (fun I : Ideal K[X] => normalize (Submodule.IsPrincipal.generator I))
    (sequenceAnnihilator_translate P hP f hrec a)

theorem minimalAnnihilator_flat_translate {N : ℕ} (w : ℕ → ℕ) (f : ℕ → ℚ)
    (hf : shiftAction ((flatPolynomial N w).map (Int.castRingHom ℚ)) f = 0) (a : ℕ) :
    minimalAnnihilator (fun n => f (a + n)) = minimalAnnihilator f := by
  apply minimalAnnihilator_translate _ _ f hf a
  simp only [coeff_map, flatPolynomial_coeff_zero, map_one, ne_eq, one_ne_zero, not_false_eq_true]

end Erdos345
