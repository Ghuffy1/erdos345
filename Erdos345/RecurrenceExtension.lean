import Erdos345.ZeroRuns
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.LinearCombination

namespace Erdos345

open Finset Polynomial

noncomputable def polynomialRecurrence (p : ℤ[X]) : LinearRecurrence ℤ where
  order := p.natDegree
  coeffs i := -p.leadingCoeff * p.coeff i

theorem polynomialRecurrence_sum (p : ℤ[X]) (f : ℕ → ℤ) (n : ℕ) :
    (∑ i : Fin (polynomialRecurrence p).order, (polynomialRecurrence p).coeffs i * f (n + i)) =
      -p.leadingCoeff * ∑ i ∈ range p.natDegree, p.coeff i * f (n + i) := by
  change (∑ i : Fin p.natDegree, (-p.leadingCoeff * p.coeff i) * f (n + i)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => (-p.leadingCoeff * p.coeff i) * f (n + i))]
  simp only [mul_assoc, mul_sum]

theorem shiftAction_last (p : ℤ[X]) (f : ℕ → ℤ) (n : ℕ) :
    shiftAction p f n =
      (∑ i ∈ range p.natDegree, p.coeff i * f (n + i)) + p.leadingCoeff * f (n + p.natDegree) := by
  rw [shiftAction_sum, sum_range_succ, coeff_natDegree]

theorem polynomialRecurrence_iff (p : ℤ[X]) (hp : p.leadingCoeff ^ 2 = 1)
    (f : ℕ → ℤ) :
    (polynomialRecurrence p).IsSolution f ↔ shiftAction p f = 0 := by
  constructor
  · intro h
    funext n
    rw [shiftAction_last]
    have hn := h n
    rw [polynomialRecurrence_sum] at hn
    change f (n + p.natDegree) = _ at hn
    rw [hn]
    dsimp only [Pi.zero_apply]
    linear_combination -(∑ i ∈ range p.natDegree, p.coeff i * f (n + i)) * hp
  · intro h n
    rw [polynomialRecurrence_sum]
    change f (n + p.natDegree) = _
    have hn := congrFun h n
    rw [shiftAction_last] at hn
    dsimp only [Pi.zero_apply] at hn
    linear_combination p.leadingCoeff * hn - f (n + p.natDegree) * hp

theorem shiftAction_translate (p : ℤ[X]) (f : ℕ → ℤ) (a n : ℕ) :
    shiftAction p (fun j => f (a + j)) n = shiftAction p f (a + n) := by
  simp only [shiftAction_sum, Nat.add_assoc]

theorem local_solution_agrees_mkSol (p : ℤ[X]) (hp : p.leadingCoeff ^ 2 = 1)
    (m : ℕ → ℤ) (L : ℕ) (hrec : ∀ n < L, shiftAction p m n = 0) :
    ∀ j < p.natDegree + L,
      (polynomialRecurrence p).mkSol (fun i => m i) j = m j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hsmall : j < p.natDegree
    · exact (polynomialRecurrence p).mkSol_eq_init (fun i => m i) ⟨j, hsmall⟩
    have hD : p.natDegree ≤ j := Nat.le_of_not_gt hsmall
    have hstart : j - p.natDegree < L := by omega
    have hm := hrec (j - p.natDegree) hstart
    rw [shiftAction_last, Nat.sub_add_cancel hD] at hm
    have hvalue : m j = -p.leadingCoeff *
        ∑ i ∈ range p.natDegree, p.coeff i * m (j - p.natDegree + i) := by
      linear_combination p.leadingCoeff * hm - m j * hp
    have hf := (polynomialRecurrence p).is_sol_mkSol (fun i => m i) (j - p.natDegree)
    rw [polynomialRecurrence_sum] at hf
    simp only [polynomialRecurrence, Nat.sub_add_cancel hD] at hf
    have hf' : (polynomialRecurrence p).mkSol (fun i => m i) j =
        -p.leadingCoeff * ∑ i ∈ range p.natDegree,
          p.coeff i * (polynomialRecurrence p).mkSol (fun i => m i) (j - p.natDegree + i) := hf
    rw [hf', hvalue]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hij : j - p.natDegree + i < j := by
      have := mem_range.mp hi
      omega
    rw [ih _ hij (by omega)]

noncomputable def prependRecurrence (p : ℤ[X]) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => -(∑ i ∈ range p.natDegree, p.coeff (i + 1) * f i)
  | n + 1 => f n

theorem prependRecurrence_solution (p : ℤ[X]) (hp : p.coeff 0 = 1)
    (f : ℕ → ℤ) (hf : shiftAction p f = 0) :
    shiftAction p (prependRecurrence p f) = 0 := by
  funext n
  cases n with
  | zero =>
    rw [shiftAction_sum, sum_range_succ']
    simp [hp, prependRecurrence]
  | succ n =>
    have hn := congrFun hf n
    simpa only [shiftAction_sum, Nat.succ_add, prependRecurrence, Pi.zero_apply] using hn

/-- Constant coefficient one allows any global solution to be extended one
position backwards, and iterating this gives any prescribed finite shift. -/
theorem exists_unshifted_recurrence (p : ℤ[X]) (hp : p.coeff 0 = 1)
    (f : ℕ → ℤ) (hf : shiftAction p f = 0) (a : ℕ) :
    ∃ g : ℕ → ℤ, shiftAction p g = 0 ∧ ∀ n, g (a + n) = f n := by
  induction a with
  | zero => exact ⟨f, hf, fun n => by simp⟩
  | succ a ih =>
    obtain ⟨g, hg, hmatch⟩ := ih
    refine ⟨prependRecurrence p g, prependRecurrence_solution p hp g hg, ?_⟩
    intro n
    simpa only [Nat.succ_add, prependRecurrence] using hmatch n

/-- A finite exact recurrence run extends to a global integer solution, with
all the run's initial data retained. Both endpoint unit conditions are explicit. -/
theorem exists_integral_recurrence_extension (p : ℤ[X])
    (hp0 : p.coeff 0 = 1) (hpD : p.leadingCoeff ^ 2 = 1)
    (m : ℕ → ℤ) (a L : ℕ) (hrec : ∀ n < L, shiftAction p m (a + n) = 0) :
    ∃ g : ℕ → ℤ, shiftAction p g = 0 ∧
      ∀ j < p.natDegree + L, g (a + j) = m (a + j) := by
  let init : Fin (polynomialRecurrence p).order → ℤ := fun i => m (a + i)
  let f := (polynomialRecurrence p).mkSol init
  have hf : shiftAction p f = 0 :=
    (polynomialRecurrence_iff p hpD f).mp ((polynomialRecurrence p).is_sol_mkSol init)
  obtain ⟨g, hg, hmatch⟩ := exists_unshifted_recurrence p hp0 f hf a
  refine ⟨g, hg, ?_⟩
  intro j hj
  rw [hmatch]
  exact local_solution_agrees_mkSol p hpD (fun n => m (a + n)) L
    (fun n hn => by rw [shiftAction_translate]; exact hrec n hn) j hj

theorem flatPolynomial_integral_extension (N : ℕ) (a : ℕ → ℕ)
    (m : ℕ → ℤ) (b L : ℕ)
    (hrec : ∀ n < L, shiftAction (flatPolynomial N a) m (b + n) = 0) :
    ∃ g : ℕ → ℤ, shiftAction (flatPolynomial N a) g = 0 ∧
      ∀ j < (flatPolynomial N a).natDegree + L, g (b + j) = m (b + j) := by
  apply exists_integral_recurrence_extension _ (flatPolynomial_coeff_zero N a) _ m b L hrec
  rw [flatPolynomial_leadingCoeff, ← pow_mul, Nat.mul_comm (weightMass N a) 2, pow_mul]
  norm_num

end Erdos345
