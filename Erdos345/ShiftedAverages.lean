import Erdos345.SimultaneousBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Erdos345

/-- Translating a finite set injectively cannot increase the total nonnegative mass. -/
theorem translated_sum_le (S U : Finset ℤ) (f : ℤ → ℚ) (t : ℤ)
    (hsub : ∀ k ∈ S, k - t ∈ U) (hf : ∀ u ∈ U, 0 ≤ f u) :
    (∑ k ∈ S, f (k - t)) ≤ ∑ u ∈ U, f u := by
  classical
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a - t = b - t → a = b := by
    intro a _ b _ h
    omega
  have himage : S.image (fun k => k - t) ⊆ U := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    exact hsub k hk
  calc
    (∑ k ∈ S, f (k - t)) = ∑ u ∈ S.image (fun k => k - t), f u :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ u ∈ U, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun u hu _ => hf u hu)

/-- A finite support removes any restriction on the amount of translation. -/
theorem translated_sum_le_support (S U : Finset ℤ) (f : ℤ → ℚ) (t : ℤ)
    (hzero : ∀ z : ℤ, z ∉ U → f z = 0) (hf : ∀ z : ℤ, 0 ≤ f z) :
    (∑ k ∈ S, f (k - t)) ≤ ∑ u ∈ U, f u := by
  classical
  let V := S.image (fun k => k - t)
  have heq : (∑ u ∈ U, f u) = ∑ u ∈ U ∪ V, f u :=
    Finset.sum_subset Finset.subset_union_left (fun z _ hz => hzero z hz)
  have hsub : ∀ k ∈ S, k - t ∈ U ∪ V := by
    intro k hk
    exact Finset.mem_union_right U (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  rw [heq]
  exact translated_sum_le S (U ∪ V) f t hsub (fun z _ => hf z)

/-- Double counting with finite support, allowing shifts beyond the start of S. -/
theorem sum_backward_prefix_le_support (S U T : Finset ℤ) (f : ℤ → ℚ)
    (hzero : ∀ z : ℤ, z ∉ U → f z = 0) (hf : ∀ z : ℤ, 0 ≤ f z) :
    (∑ k ∈ S, ∑ t ∈ T, f (k - t)) ≤
      (T.card : ℚ) * ∑ u ∈ U, f u := by
  rw [Finset.sum_comm]
  calc
    (∑ t ∈ T, ∑ k ∈ S, f (k - t)) ≤ ∑ _t ∈ T, ∑ u ∈ U, f u :=
      Finset.sum_le_sum (fun t _ => translated_sum_le_support S U f t hzero hf)
    _ = (T.card : ℚ) * ∑ u ∈ U, f u := by simp

/-- The elementary double-counting bound for a family of backward averages. -/
theorem sum_backward_prefix_le (S U T : Finset ℤ) (f : ℤ → ℚ)
    (hsub : ∀ k ∈ S, ∀ t ∈ T, k - t ∈ U)
    (hf : ∀ u ∈ U, 0 ≤ f u) :
    (∑ k ∈ S, ∑ t ∈ T, f (k - t)) ≤
      (T.card : ℚ) * ∑ u ∈ U, f u := by
  rw [Finset.sum_comm]
  calc
    (∑ t ∈ T, ∑ k ∈ S, f (k - t)) ≤ ∑ _t ∈ T, ∑ u ∈ U, f u :=
      Finset.sum_le_sum (fun t ht => translated_sum_le S U f t
        (fun k hk => hsub k hk t ht) hf)
    _ = (T.card : ℚ) * ∑ u ∈ U, f u := by simp

/-- One k simultaneously has small backward averages for every selected length.
The original divisor-function application must still supply its global mass bound
and its finite family of dyadic lengths. -/
theorem exists_simultaneous_backward_averages {ι : Type*}
    (I : Finset ι) (S U : Finset ℤ) (T : ι → Finset ℤ) (f : ℤ → ℚ)
    (hS : S.Nonempty) (hT : ∀ i ∈ I, (T i).Nonempty)
    (hsub : ∀ i ∈ I, ∀ k ∈ S, ∀ t ∈ T i, k - t ∈ U)
    (hf : ∀ u ∈ U, 0 ≤ f u) (B : ℚ)
    (hbudget : (I.card : ℚ) * (∑ u ∈ U, f u) ≤ (S.card : ℚ) * B) :
    ∃ k ∈ S, ∀ i ∈ I,
      (∑ t ∈ T i, f (k - t)) ≤ B * ((T i).card : ℚ) := by
  apply exists_simultaneous_weighted_bound I S hS
    (fun i k => ∑ t ∈ T i, f (k - t)) (fun i => ((T i).card : ℚ))
    (∑ u ∈ U, f u) B
  · intro i hi
    exact_mod_cast Finset.card_pos.mpr (hT i hi)
  · intro i hi k hk
    exact Finset.sum_nonneg (fun t ht => hf (k - t) (hsub i hi k hk t ht))
  · intro i hi
    simpa [mul_comm] using sum_backward_prefix_le S U (T i) f
      (hsub i hi) hf
  · exact hbudget

theorem exists_simultaneous_backward_averages_support {ι : Type*}
    (I : Finset ι) (S U : Finset ℤ) (T : ι → Finset ℤ) (f : ℤ → ℚ)
    (hS : S.Nonempty) (hT : ∀ i ∈ I, (T i).Nonempty)
    (hzero : ∀ z : ℤ, z ∉ U → f z = 0)
    (hf : ∀ z : ℤ, 0 ≤ f z) (B : ℚ)
    (hbudget : (I.card : ℚ) * (∑ u ∈ U, f u) ≤ (S.card : ℚ) * B) :
    ∃ k ∈ S, ∀ i ∈ I,
      (∑ t ∈ T i, f (k - t)) ≤ B * ((T i).card : ℚ) := by
  apply exists_simultaneous_weighted_bound I S hS
    (fun i k => ∑ t ∈ T i, f (k - t)) (fun i => ((T i).card : ℚ))
    (∑ u ∈ U, f u) B
  · intro i hi
    exact_mod_cast Finset.card_pos.mpr (hT i hi)
  · intro i _ k _
    exact Finset.sum_nonneg (fun t _ => hf (k - t))
  · intro i _
    simpa [mul_comm] using sum_backward_prefix_le_support S U (T i) f hzero hf
  · exact hbudget

end Erdos345
