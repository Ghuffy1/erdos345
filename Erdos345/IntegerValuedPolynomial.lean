import Erdos345.FiniteDifferences
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp

namespace Erdos345

open Polynomial

/-- The rational polynomial taking the values n.choose j on natural inputs. -/
noncomputable def binomialPolynomial (j : ℕ) : ℚ[X] :=
  C ((j.factorial : ℚ)⁻¹) * descPochhammer ℚ j

theorem binomialPolynomial_eval_nat (j n : ℕ) :
    (binomialPolynomial j).eval (n : ℚ) = (n.choose j : ℚ) := by
  have hj : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  simp only [binomialPolynomial, eval_mul, eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  exact inv_mul_cancel_left₀ hj _

theorem binomialPolynomial_eval_int (j : ℕ) (z : ℤ) :
    (binomialPolynomial j).eval (z : ℚ) = ((Ring.choose z j : ℤ) : ℚ) := by
  have hfac : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hi : (descPochhammer ℤ j).eval z = (j.factorial : ℤ) * Ring.choose z j := by
    simpa only [Polynomial.eval_eq_smeval, nsmul_eq_mul] using
      (Ring.descPochhammer_eq_factorial_smul_choose z j)
  have hq : (descPochhammer ℚ j).eval (z : ℚ) =
      (j.factorial : ℚ) * ((Ring.choose z j : ℤ) : ℚ) := by
    have hc := congrArg (fun m : ℤ => (m : ℚ)) hi
    simpa only [descPochhammer_eval_cast, Int.cast_mul, Int.cast_natCast] using hc
  simp only [binomialPolynomial, eval_mul, eval_C, hq]
  exact inv_mul_cancel_left₀ hfac _

theorem binomialPolynomial_natDegree_le (j : ℕ) :
    (binomialPolynomial j).natDegree ≤ j := by
  exact (natDegree_C_mul_le _ _).trans (by simp)

theorem binomialPolynomial_coeff_self (j : ℕ) :
    (binomialPolynomial j).coeff j = (j.factorial : ℚ)⁻¹ := by
  have hc : (descPochhammer ℚ j).coeff j = 1 := by
    simpa only [descPochhammer_natDegree] using (monic_descPochhammer ℚ j).coeff_natDegree
  simp only [binomialPolynomial, coeff_C_mul, hc, mul_one]

/-- A finite polynomial in the rational binomial basis. -/
noncomputable def newtonPolynomial (a : ℕ → ℚ) (d : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (d + 1), C (a j) * binomialPolynomial j

/-- Integer-valued means all integer inputs, including negative inputs. -/
def integerValuedPolynomial (p : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ m : ℤ, p.eval (z : ℚ) = (m : ℚ)

theorem newtonPolynomial_integerValued (a : ℕ → ℤ) (d : ℕ) :
    integerValuedPolynomial (newtonPolynomial (fun j => (a j : ℚ)) d) := by
  intro z
  refine ⟨∑ j ∈ Finset.range (d + 1), a j * Ring.choose z j, ?_⟩
  simp only [newtonPolynomial, eval_finsetSum, eval_mul, eval_C,
    binomialPolynomial_eval_int, Int.cast_sum, Int.cast_mul]

theorem newtonPolynomial_eval_nat (a : ℕ → ℚ) (d n : ℕ) :
    (newtonPolynomial a d).eval (n : ℚ) =
      ∑ j ∈ Finset.range (d + 1), a j * (n.choose j : ℚ) := by
  simp only [newtonPolynomial, eval_finsetSum, eval_mul, eval_C,
    binomialPolynomial_eval_nat]

theorem newtonPolynomial_natDegree_le (a : ℕ → ℚ) (d : ℕ) :
    (newtonPolynomial a d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans
    ((binomialPolynomial_natDegree_le j).trans (by
      have := Finset.mem_range.mp hj
      omega))

theorem newtonPolynomial_coeff_top (a : ℕ → ℚ) (d : ℕ) :
    (newtonPolynomial a d).coeff d = a d * (d.factorial : ℚ)⁻¹ := by
  rw [newtonPolynomial, finsetSum_coeff, Finset.sum_range_succ]
  simp only [coeff_C_mul]
  have hzero : (∑ j ∈ Finset.range d, a j * (binomialPolynomial j).coeff d) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hdj : (binomialPolynomial j).natDegree < d :=
      (binomialPolynomial_natDegree_le j).trans_lt (Finset.mem_range.mp hj)
    rw [coeff_eq_zero_of_natDegree_lt hdj, mul_zero]
  rw [hzero, zero_add, binomialPolynomial_coeff_self]

theorem newtonPolynomial_eval_initial (a : ℕ → ℚ) {d n : ℕ} (hn : n ≤ d) :
    (newtonPolynomial a d).eval (n : ℚ) = newtonEval a n := by
  rw [newtonPolynomial_eval_nat, newtonEval]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
  intro j _ hj
  have hnj : n < j := by
    have : ¬j < n + 1 := fun h => hj (Finset.mem_range.mpr h)
    omega
  simp [Nat.choose_eq_zero_of_lt hnj]

/-- Rational polynomials of degree at most d are determined by d+1 consecutive values. -/
theorem polynomial_eq_of_eval_range {p q : ℚ[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (he : ∀ n : ℕ, n ≤ d → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  classical
  by_contra hne
  have hr : p - q ≠ 0 := sub_ne_zero.mpr hne
  let S : Finset ℚ := (Finset.range (d + 1)).image (fun n : ℕ => (n : ℚ))
  have hcard : S.card = d + 1 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective, Finset.card_range]
    exact Nat.cast_injective
  have hroots : S.val ⊆ (p - q).roots := by
    intro x hx
    change x ∈ (Finset.range (d + 1)).image (fun n : ℕ => (n : ℚ)) at hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    apply (Polynomial.mem_roots hr).mpr
    rw [Polynomial.IsRoot, eval_sub, he n (by
      have := Finset.mem_range.mp hn
      omega), sub_self]
  have hsize := Polynomial.card_le_degree_of_subset_roots hroots
  have hdegree : (p - q).natDegree ≤ d :=
    (natDegree_sub_le p q).trans (max_le hp hq)
  rw [hcard] at hsize
  omega

/-- Every rational polynomial has its finite Newton expansion. -/
theorem polynomial_eq_newtonPolynomial (p : ℚ[X]) {d : ℕ} (hp : p.natDegree ≤ d) :
    p = newtonPolynomial
      (fun j => iteratedDifference j (fun n : ℕ => p.eval (n : ℚ)) 0) d := by
  apply polynomial_eq_of_eval_range hp (newtonPolynomial_natDegree_le _ _)
  intro n hn
  rw [newtonPolynomial_eval_initial _ hn, newton_forward_formula]

/-- The top finite difference equals factorial times the corresponding coefficient,
even when the polynomial has degree strictly below the chosen index. -/
theorem polynomial_top_difference (p : ℚ[X]) {d : ℕ} (hp : p.natDegree ≤ d) :
    iteratedDifference d (fun n : ℕ => p.eval (n : ℚ)) 0 =
      (d.factorial : ℚ) * p.coeff d := by
  have hc := congrArg (fun r : ℚ[X] => r.coeff d) (polynomial_eq_newtonPolynomial p hp)
  rw [newtonPolynomial_coeff_top] at hc
  have hfac : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  rw [hc]
  field_simp

def truncateCoefficients {R : Type*} [Zero R] (a : ℕ → R) (d j : ℕ) : R :=
  if j ≤ d then a j else 0

theorem newtonEval_truncate_eq_sum {R : Type*} [Semiring R]
    (a : ℕ → R) (d n : ℕ) :
    newtonEval (truncateCoefficients a d) n =
      ∑ j ∈ Finset.range (d + 1), a j * (n.choose j : R) := by
  unfold newtonEval
  by_cases hn : n ≤ d
  · trans ∑ j ∈ Finset.range (n + 1), a j * (n.choose j : R)
    · apply Finset.sum_congr rfl
      intro j hj
      have hjd : j ≤ d := by
        have := Finset.mem_range.mp hj
        omega
      simp [truncateCoefficients, hjd]
    · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
      intro j _ hj
      have hnj : n < j := by
        have : ¬j < n + 1 := fun h => hj (Finset.mem_range.mpr h)
        omega
      simp [Nat.choose_eq_zero_of_lt hnj]
  · symm
    trans ∑ j ∈ Finset.range (d + 1), truncateCoefficients a d j * (n.choose j : R)
    · apply Finset.sum_congr rfl
      intro j hj
      simp [truncateCoefficients, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)]
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      have hjd : ¬j ≤ d := by
        intro hle
        exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [truncateCoefficients, hjd]

theorem newtonPolynomial_eval_truncate (a : ℕ → ℚ) (d n : ℕ) :
    (newtonPolynomial a d).eval (n : ℚ) =
      newtonEval (truncateCoefficients a d) n := by
  by_cases hn : n ≤ d
  · rw [newtonPolynomial_eval_initial a hn]
    apply Finset.sum_congr rfl
    intro j hj
    have hjd : j ≤ d := by
      have := Finset.mem_range.mp hj
      omega
    simp [truncateCoefficients, hjd]
  · rw [newtonPolynomial_eval_nat, newtonEval]
    trans ∑ j ∈ Finset.range (d + 1), truncateCoefficients a d j * (n.choose j : ℚ)
    · apply Finset.sum_congr rfl
      intro j hj
      have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp [truncateCoefficients, hjd]
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      have hjd : ¬j ≤ d := by
        intro hle
        exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [truncateCoefficients, hjd]

theorem polynomial_difference_coefficient_zero (p : ℚ[X]) {d j : ℕ}
    (hp : p.natDegree ≤ d) (hj : d < j) :
    iteratedDifference j (fun n : ℕ => p.eval (n : ℚ)) 0 = 0 := by
  let a : ℕ → ℚ := fun i => iteratedDifference i (fun n : ℕ => p.eval (n : ℚ)) 0
  have heq : newtonEval a = newtonEval (truncateCoefficients a d) := by
    funext n
    calc
      newtonEval a n = p.eval (n : ℚ) := newton_forward_formula _ _
      _ = (newtonPolynomial a d).eval (n : ℚ) :=
        congrArg (fun r : ℚ[X] => r.eval (n : ℚ)) (polynomial_eq_newtonPolynomial p hp)
      _ = newtonEval (truncateCoefficients a d) n := newtonPolynomial_eval_truncate a d n
  have hc := congrFun (newtonEval_injective heq) j
  simpa [a, truncateCoefficients, Nat.not_le_of_gt hj] using hc

theorem polynomial_iteratedDifference_zero (p : ℚ[X]) {d s : ℕ}
    (hp : p.natDegree ≤ d) (hs : d < s) (n : ℕ) :
    iteratedDifference s (fun m : ℕ => p.eval (m : ℚ)) n = 0 := by
  have hseq : (fun m : ℕ => p.eval (m : ℚ)) =
      newtonEval (fun j => iteratedDifference j (fun m : ℕ => p.eval (m : ℚ)) 0) := by
    funext m
    exact (newton_forward_formula (R := ℚ) (fun r : ℕ => p.eval (r : ℚ)) m).symm
  rw [hseq, iteratedDifference_newtonEval]
  apply Finset.sum_eq_zero
  intro j _
  dsimp only
  rw [polynomial_difference_coefficient_zero p hp (by omega), zero_mul]

end Erdos345
