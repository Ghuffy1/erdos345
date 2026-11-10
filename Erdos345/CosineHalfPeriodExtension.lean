import Erdos345.ProfileCosinePositivity
import Mathlib.Algebra.Field.Periodic

namespace Erdos345

theorem cosine_nonneg_of_half_period (n : ℕ) (w : ℕ → ℝ) (a : ℝ)
    (h : ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      0 ≤ a + ∑ i ∈ Finset.range n, w i * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) :
    ∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range n, w i * Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
  let f : ℝ → ℝ := fun θ => a + ∑ i ∈ Finset.range n, w i * Real.cos (((i + 1 : ℕ) : ℝ) * θ)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp only [f]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [mul_add, Real.cos_add_nat_mul_two_pi]
  have he : ∀ θ, f (-θ) = f θ := by
    intro θ
    dsimp only [f]
    simp only [mul_neg, Real.cos_neg]
  intro θ
  obtain ⟨y, hy, hf⟩ := hp.exists_mem_Ico (by positivity : (0 : ℝ) < 2 * Real.pi) θ (-Real.pi)
  have habs : |y| ≤ Real.pi := by
    apply abs_le.mpr
    constructor
    · exact hy.1
    · linarith [hy.2]
  have hval := h |y| (abs_nonneg y) habs
  have heq : f |y| = f y := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_nonpos hy0, he]
  change 0 ≤ f θ
  rw [hf, ← heq]
  exact hval

end Erdos345
