import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Erdos345

theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), f i) =
      (∑ i ∈ Finset.range k, f (2 * i)) + (∑ i ∈ Finset.range k, f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ac_rfl

theorem alternating_span_balance (L : ℕ → ℕ) (k l : ℕ)
    (hmono : ∀ i j, i ≤ j → j < 2 * k → L i ≤ L j)
    (hbound : ∀ i < 2 * k, L i ≤ l) :
    (∑ i ∈ Finset.range k, L (2 * i)) ≤ (∑ i ∈ Finset.range k, L (2 * i + 1)) ∧
      (∑ i ∈ Finset.range k, L (2 * i + 1)) ≤ (∑ i ∈ Finset.range k, L (2 * i)) + l := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact hmono _ _ (by omega) (by have := Finset.mem_range.mp hi; omega)
  · have htel : ∀ h ≤ k,
        (∑ i ∈ Finset.range h, L (2 * i + 1)) + L 0 ≤
          (∑ i ∈ Finset.range h, L (2 * i)) + L (2 * h - 1) := by
      intro h
      induction h with
      | zero => simp
      | succ h ih =>
        intro hh
        have hi := ih (by omega)
        have hnext : L (2 * h - 1) ≤ L (2 * h) := hmono _ _ (by omega) (by omega)
        rw [Finset.sum_range_succ, Finset.sum_range_succ,
          show 2 * (h + 1) - 1 = 2 * h + 1 by omega]
        omega
    by_cases hk : k = 0
    · subst k
      simp
    · have ht := htel k le_rfl
      have hb := hbound (2 * k - 1) (by omega)
      omega

end Erdos345
