import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace Erdos345

/-- The integral Newton coefficient j! S(k,j) of a monomial. -/
def powerCoefficient (k j : ℕ) : ℕ :=
  j.factorial * Nat.stirlingSecond k j

theorem powerCoefficient_eq_zero {k j : ℕ} (h : k < j) :
    powerCoefficient k j = 0 := by
  simp [powerCoefficient, Nat.stirlingSecond_eq_zero_of_lt h]

theorem pow_newton_expansion (n k : ℕ) :
    n ^ k = ∑ j ∈ Finset.range (k + 1), powerCoefficient k j * n.choose j := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_congr rfl
  intro j _
  simp only [powerCoefficient, Nat.descFactorial_eq_factorial_mul_choose]
  ac_rfl

/-- Evaluation of an arbitrary Newton coefficient sequence at a natural number.
All terms beyond n vanish, so the definition needs no support assumption. -/
def newtonEval {R : Type*} [Semiring R] (a : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), a j * (n.choose j : R)

theorem newtonEval_injective {R : Type*} [Ring R] :
    Function.Injective (newtonEval (R := R)) := by
  intro a b hab
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := congrFun hab n
    simp only [newtonEval, Finset.sum_range_succ, Nat.choose_self,
      Nat.cast_one, mul_one] at he
    have hs : (∑ j ∈ Finset.range n, a j * (n.choose j : R)) =
        ∑ j ∈ Finset.range n, b j * (n.choose j : R) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    rw [hs] at he
    exact add_left_cancel he

theorem newtonEval_powerCoefficient {R : Type*} [Semiring R] (k n : ℕ) :
    newtonEval (fun j => (powerCoefficient k j : R)) n = (n : R) ^ k := by
  have hexpand : (n : R) ^ k =
      ∑ j ∈ Finset.range (k + 1), (powerCoefficient k j : R) * (n.choose j : R) := by
    have hc := congrArg (fun a : ℕ => (a : R)) (pow_newton_expansion n k)
    simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using hc
  rw [newtonEval, hexpand]
  by_cases hnk : n ≤ k
  · apply Finset.sum_subset
    · exact Finset.range_mono (Nat.succ_le_succ hnk)
    · intro j _ hj
      have hnj : n < j := by
        have : ¬ j < n + 1 := fun h => hj (Finset.mem_range.mpr h)
        omega
      simp [Nat.choose_eq_zero_of_lt hnj]
  · symm
    apply Finset.sum_subset
    · exact Finset.range_mono (Nat.succ_le_succ (Nat.le_of_not_ge hnk))
    · intro j _ hj
      have hkj : k < j := by
        have : ¬ j < k + 1 := fun h => hj (Finset.mem_range.mpr h)
        omega
      simp [powerCoefficient_eq_zero hkj]

/-- Modular reduction in the integral Newton basis.
The bridge to rational integer-valued polynomials is a separate obligation. -/
def hasNewtonReduction (q k d : ℕ) : Prop :=
  ∃ a : ℕ → ZMod q,
    (∀ j : ℕ, d < j → a j = 0) ∧
    ∀ n : ℕ, newtonEval a n = (n : ZMod q) ^ k

theorem hasNewtonReduction_iff (q k d : ℕ) :
    hasNewtonReduction q k d ↔
      ∀ j : ℕ, d < j → q ∣ powerCoefficient k j := by
  constructor
  · rintro ⟨a, ha, heval⟩
    have heq : a = fun j => (powerCoefficient k j : ZMod q) := by
      apply newtonEval_injective
      funext n
      exact (heval n).trans (newtonEval_powerCoefficient k n).symm
    intro j hj
    apply (ZMod.natCast_eq_zero_iff (powerCoefficient k j) q).mp
    rw [← congrFun heq j]
    exact ha j hj
  · intro htail
    refine ⟨fun j => (powerCoefficient k j : ZMod q), ?_, ?_⟩
    · intro j hj
      exact (ZMod.natCast_eq_zero_iff (powerCoefficient k j) q).mpr (htail j hj)
    · exact newtonEval_powerCoefficient k

end Erdos345
