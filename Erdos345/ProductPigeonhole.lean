import Erdos345.LogDenominatorBound

namespace Erdos345

open Finset

/-- A product lower bound and a denominator budget force one factor to be
at least the corresponding exponential threshold. -/
theorem exists_factor_ge_exp_neg {I : Type*} [Fintype I] [Nonempty I]
    (g : I → ℝ) (hg : ∀ i, 0 < g i) (D B : ℝ) (hD : 0 < D)
    (hproduct : 1 ≤ (∏ i, g i) * D)
    (hbudget : Real.log D ≤ (Fintype.card I : ℝ) * B) :
    ∃ i, Real.exp (-B) ≤ g i := by
  classical
  have hp : (∏ i, g i) ≠ 0 := ne_of_gt (prod_pos (fun i _ => hg i))
  have hlog : 0 ≤ (∑ i, Real.log (g i)) + Real.log D := by
    have hh := Real.log_nonneg hproduct
    rwa [Real.log_mul hp (ne_of_gt hD), Real.log_prod (fun i _ => ne_of_gt (hg i))] at hh
  by_contra h
  push Not at h
  have hstrict : (∑ i, Real.log (g i)) < ∑ _i : I, -B := by
    apply sum_lt_sum
    · intro i _
      have hh := Real.log_lt_log (hg i) (h i)
      rw [Real.log_exp] at hh
      exact hh.le
    · obtain ⟨i⟩ := ‹Nonempty I›
      refine ⟨i, mem_univ i, ?_⟩
      have hh := Real.log_lt_log (hg i) (h i)
      rwa [Real.log_exp] at hh
  simp only [sum_const, card_univ, nsmul_eq_mul] at hstrict
  nlinarith

end Erdos345
