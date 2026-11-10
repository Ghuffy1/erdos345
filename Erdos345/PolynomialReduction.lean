import Erdos345.IntegerValuedPolynomial
import Erdos345.ReductionModuli

namespace Erdos345

open Polynomial

/-- Reduction of n^k modulo q by a rational polynomial of degree at most d.
The reducing polynomial is integer-valued on every integer, not only sampled inputs. -/
def hasIntegerPolynomialReduction (q k d : ℕ) : Prop :=
  ∃ p : ℚ[X], p.natDegree ≤ d ∧ integerValuedPolynomial p ∧
    ∀ n : ℕ, ∃ z : ℤ, p.eval (n : ℚ) = (z : ℚ) ∧
      (q : ℤ) ∣ (n : ℤ) ^ k - z

theorem polynomialReduction_tail_divisibility {q k d : ℕ}
    (h : hasIntegerPolynomialReduction q k d) :
    ∀ j : ℕ, d < j → q ∣ powerCoefficient k j := by
  classical
  obtain ⟨p, hp, _hInteger, hmod⟩ := h
  let f : ℕ → ℤ := fun n => Classical.choose (hmod n)
  have hf : ∀ n : ℕ, p.eval (n : ℚ) = (f n : ℚ) ∧
      (q : ℤ) ∣ (n : ℤ) ^ k - f n := by
    intro n
    exact Classical.choose_spec (hmod n)
  have hQ : (fun n : ℕ => (f n : ℚ)) = (fun n : ℕ => p.eval (n : ℚ)) := by
    funext n
    exact (hf n).1.symm
  have hM : (fun n : ℕ => (f n : ZMod q)) = (fun n : ℕ => (n : ZMod q) ^ k) := by
    funext n
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) ^ k - f n) q).mpr (hf n).2
    have hz' : (n : ZMod q) ^ k - (f n : ZMod q) = 0 := by
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using hz
    exact (sub_eq_zero.mp hz').symm
  intro j hj
  have hmapQ := map_iteratedDifference (Int.castRingHom ℚ) f j 0
  change ((iteratedDifference j f 0 : ℤ) : ℚ) =
    iteratedDifference j (fun n : ℕ => (f n : ℚ)) 0 at hmapQ
  rw [hQ, polynomial_difference_coefficient_zero p hp hj] at hmapQ
  have hzero : iteratedDifference j f 0 = 0 := by exact_mod_cast hmapQ
  have hmapM := map_iteratedDifference (Int.castRingHom (ZMod q)) f j 0
  change ((iteratedDifference j f 0 : ℤ) : ZMod q) =
    iteratedDifference j (fun n : ℕ => (f n : ZMod q)) 0 at hmapM
  rw [hzero, Int.cast_zero, hM, iteratedDifference_power_zero] at hmapM
  exact (ZMod.natCast_eq_zero_iff (powerCoefficient k j) q).mp hmapM.symm

theorem polynomialReduction_of_tail_divisibility {q k d : ℕ}
    (htail : ∀ j : ℕ, d < j → q ∣ powerCoefficient k j) :
    hasIntegerPolynomialReduction q k d := by
  let a : ℕ → ℤ := fun j => (powerCoefficient k j : ℤ)
  let p : ℚ[X] := newtonPolynomial (fun j => (a j : ℚ)) d
  refine ⟨p, newtonPolynomial_natDegree_le _ _, newtonPolynomial_integerValued a d, ?_⟩
  intro n
  let z : ℤ := ∑ j ∈ Finset.range (d + 1), a j * (n.choose j : ℤ)
  refine ⟨z, ?_, ?_⟩
  · simp only [p, z, newtonPolynomial_eval_nat, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  · let c : ℕ → ZMod q := fun j => (powerCoefficient k j : ZMod q)
    have htrunc : truncateCoefficients c d = c := by
      funext j
      by_cases hj : j ≤ d
      · simp [truncateCoefficients, hj]
      · have hz : c j = 0 :=
          (ZMod.natCast_eq_zero_iff (powerCoefficient k j) q).mpr (htail j (by omega))
        simp [truncateCoefficients, hj, hz]
    have hzmod : (z : ZMod q) = (n : ZMod q) ^ k := by
      calc
        (z : ZMod q) = ∑ j ∈ Finset.range (d + 1), c j * (n.choose j : ZMod q) := by
          simp only [z, a, c, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
        _ = newtonEval (truncateCoefficients c d) n :=
          (newtonEval_truncate_eq_sum c d n).symm
        _ = newtonEval c n := by rw [htrunc]
        _ = (n : ZMod q) ^ k := newtonEval_powerCoefficient k n
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub z ((n : ℤ) ^ k) q).mp
    simpa only [Int.cast_pow, Int.cast_natCast] using hzmod

/-- Exact equivalence between rational integer-valued polynomial reduction
and divisibility by the gcd of the higher Newton coefficients. -/
theorem hasIntegerPolynomialReduction_iff_dvd (q k d : ℕ) :
    hasIntegerPolynomialReduction q k d ↔ q ∣ reductionModulus k d :=
  ⟨fun h => (dvd_reductionModulus_iff q k d).mpr (polynomialReduction_tail_divisibility h),
    fun h => polynomialReduction_of_tail_divisibility
      ((dvd_reductionModulus_iff q k d).mp h)⟩

theorem X_pow_eq_newtonPolynomial (k : ℕ) :
    (X : ℚ[X]) ^ k = newtonPolynomial (fun j => (powerCoefficient k j : ℚ)) k := by
  apply polynomial_eq_of_eval_range (by simp) (newtonPolynomial_natDegree_le _ _)
  intro n _
  rw [eval_pow, eval_X, newtonPolynomial_eval_nat]
  have h := congrArg (fun x : ℕ => (x : ℚ)) (pow_newton_expansion n k)
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using h

theorem integer_power_newton_expansion (k : ℕ) (n : ℤ) :
    n ^ k = ∑ j ∈ Finset.range (k + 1),
      (powerCoefficient k j : ℤ) * Ring.choose n j := by
  have h := congrArg (fun p : ℚ[X] => p.eval (n : ℚ)) (X_pow_eq_newtonPolynomial k)
  simp only [eval_pow, eval_X, newtonPolynomial, eval_finsetSum, eval_mul, eval_C,
    binomialPolynomial_eval_int] at h
  exact_mod_cast h

/-- The global version of the reduction condition, on every integer input. -/
def hasGlobalIntegerPolynomialReduction (q k d : ℕ) : Prop :=
  ∃ p : ℚ[X], p.natDegree ≤ d ∧ integerValuedPolynomial p ∧
    ∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = (z : ℚ) ∧ (q : ℤ) ∣ n ^ k - z

theorem globalPolynomialReduction_to_nat {q k d : ℕ}
    (h : hasGlobalIntegerPolynomialReduction q k d) :
    hasIntegerPolynomialReduction q k d := by
  obtain ⟨p, hp, hInt, hmod⟩ := h
  refine ⟨p, hp, hInt, ?_⟩
  intro n
  simpa only [Int.cast_natCast] using hmod (n : ℤ)

theorem globalPolynomialReduction_of_tail_divisibility {q k d : ℕ}
    (htail : ∀ j : ℕ, d < j → q ∣ powerCoefficient k j) :
    hasGlobalIntegerPolynomialReduction q k d := by
  classical
  by_cases hkd : k ≤ d
  · refine ⟨(X : ℚ[X]) ^ k, by simpa using hkd, ?_, ?_⟩
    · intro n
      exact ⟨n ^ k, by simp⟩
    · intro n
      exact ⟨n ^ k, by simp, by simp⟩
  · have hdk : d ≤ k := by omega
    let a : ℕ → ℤ := fun j => (powerCoefficient k j : ℤ)
    let p : ℚ[X] := newtonPolynomial (fun j => (a j : ℚ)) d
    refine ⟨p, newtonPolynomial_natDegree_le _ _, newtonPolynomial_integerValued a d, ?_⟩
    intro n
    let z : ℤ := ∑ j ∈ Finset.range (d + 1), a j * Ring.choose n j
    refine ⟨z, ?_, ?_⟩
    · simp only [p, z, newtonPolynomial, eval_finsetSum, eval_mul, eval_C,
        binomialPolynomial_eval_int, Int.cast_sum, Int.cast_mul]
    · have hprefix :
          (∑ j ∈ Finset.range (d + 1),
            (powerCoefficient k j : ZMod q) * (Ring.choose n j : ℤ)) =
          ∑ j ∈ Finset.range (k + 1),
            (powerCoefficient k j : ZMod q) * (Ring.choose n j : ℤ) := by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdk))
        intro j _ hj
        have hjd : d < j := by
          have : ¬j < d + 1 := fun hh => hj (Finset.mem_range.mpr hh)
          omega
        have hzj : (powerCoefficient k j : ZMod q) = 0 :=
          (ZMod.natCast_eq_zero_iff (powerCoefficient k j) q).mpr (htail j hjd)
        simp [hzj]
      have hfull :
          (∑ j ∈ Finset.range (k + 1),
            (powerCoefficient k j : ZMod q) * (Ring.choose n j : ℤ)) =
          (n : ZMod q) ^ k := by
        have h := congrArg (fun z : ℤ => (z : ZMod q)) (integer_power_newton_expansion k n)
        simpa only [Int.cast_pow, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h.symm
      have hzmod : (z : ZMod q) = ((n ^ k : ℤ) : ZMod q) := by
        simp only [z, a, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
        exact hprefix.trans hfull
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub z (n ^ k) q).mp hzmod

theorem hasGlobalIntegerPolynomialReduction_iff_dvd (q k d : ℕ) :
    hasGlobalIntegerPolynomialReduction q k d ↔ q ∣ reductionModulus k d :=
  ⟨fun h => (hasIntegerPolynomialReduction_iff_dvd q k d).mp
      (globalPolynomialReduction_to_nat h),
    fun h => globalPolynomialReduction_of_tail_divisibility
      ((dvd_reductionModulus_iff q k d).mp h)⟩

end Erdos345
