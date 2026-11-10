import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

namespace Erdos345

/-- A finite union/averaging bound: one parameter obeys every component bound.
This is an elementary selection lemma, not a hypothesis about the final result. -/
theorem exists_simultaneous_bound {ι κ : Type*}
    (I : Finset ι) (S : Finset κ) (hS : S.Nonempty)
    (w : ι → κ → ℚ) (M B : ℚ)
    (hw : ∀ i ∈ I, ∀ k ∈ S, 0 ≤ w i k)
    (hm : ∀ i ∈ I, ∑ k ∈ S, w i k ≤ M)
    (hbudget : (I.card : ℚ) * M ≤ (S.card : ℚ) * B) :
    ∃ k ∈ S, ∀ i ∈ I, w i k ≤ B := by
  classical
  by_contra hnone
  push Not at hnone
  have hbad : ∀ k ∈ S, B < ∑ i ∈ I, w i k := by
    intro k hk
    obtain ⟨i, hi, hlt⟩ := hnone k hk
    exact hlt.trans_le (Finset.single_le_sum (fun j hj => hw j hj k hk) hi)
  obtain ⟨k₀, hk₀⟩ := hS
  have hstrict : (∑ k ∈ S, B) < ∑ k ∈ S, ∑ i ∈ I, w i k :=
    Finset.sum_lt_sum (fun k hk => (hbad k hk).le) ⟨k₀, hk₀, hbad k₀ hk₀⟩
  have hupper : (∑ k ∈ S, ∑ i ∈ I, w i k) ≤ (I.card : ℚ) * M := by
    rw [Finset.sum_comm]
    calc
      (∑ i ∈ I, ∑ k ∈ S, w i k) ≤ ∑ i ∈ I, M :=
        Finset.sum_le_sum (fun i hi => hm i hi)
      _ = (I.card : ℚ) * M := by simp
  have hlower : (S.card : ℚ) * B < ∑ k ∈ S, ∑ i ∈ I, w i k := by
    simpa using hstrict
  exact (not_lt_of_ge hbudget) (hlower.trans_le hupper)

/-- The weighted version applies to prefix sums divided by their lengths. -/
theorem exists_simultaneous_weighted_bound {ι κ : Type*}
    (I : Finset ι) (S : Finset κ) (hS : S.Nonempty)
    (A : ι → κ → ℚ) (d : ι → ℚ) (M B : ℚ)
    (hd : ∀ i ∈ I, 0 < d i)
    (hA : ∀ i ∈ I, ∀ k ∈ S, 0 ≤ A i k)
    (hm : ∀ i ∈ I, ∑ k ∈ S, A i k ≤ M * d i)
    (hbudget : (I.card : ℚ) * M ≤ (S.card : ℚ) * B) :
    ∃ k ∈ S, ∀ i ∈ I, A i k ≤ B * d i := by
  obtain ⟨k, hk, hbound⟩ :=
    exists_simultaneous_bound I S hS (fun i k => A i k / d i) M B
      (fun i hi k hk => div_nonneg (hA i hi k hk) (hd i hi).le)
      (fun i hi => by
        rw [← Finset.sum_div]
        exact (div_le_iff₀ (hd i hi)).mpr (hm i hi)) hbudget
  exact ⟨k, hk, fun i hi => (div_le_iff₀ (hd i hi)).mp (hbound i hi)⟩

end Erdos345
