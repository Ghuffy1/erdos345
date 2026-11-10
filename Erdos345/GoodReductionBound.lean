import Erdos345.GoodDegreeSelection
import Erdos345.ReductionEnvelope

namespace Erdos345

/-- One degree in each dyadic interval satisfies a simultaneous logarithmic
bound for every proper reduction degree. This uses only the global divisor mean. -/
theorem exists_good_reduction_degree (Y : ℕ) (hY : 0 < Y) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧ ∀ d : ℕ, 0 < d → d < k →
      Real.log (reductionModulus k d : ℝ) ≤
        (d : ℝ) * Real.log ((2 * k : ℕ) : ℝ) +
          (4 * (d : ℝ) * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) *
            (harmonic (2 * Y) : ℝ)) * Real.log (k : ℝ) := by
  obtain ⟨k, hkY, hk2Y, hgood⟩ := exists_good_degree Y hY
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro d hd hdk
  have hsumQ :
      ((∑ i ∈ Finset.range d, divisorCount (k - (i + 1)) : ℕ) : ℚ) ≤
        4 * (d : ℚ) * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℚ) * harmonic (2 * Y) := by
    simpa only [Nat.cast_sum, Nat.sub_sub] using hgood d hd hdk
  have hsumR :
      ((∑ i ∈ Finset.range d, divisorCount (k - (i + 1)) : ℕ) : ℝ) ≤
        4 * (d : ℝ) * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) *
          (harmonic (2 * Y) : ℝ) := by exact_mod_cast hsumQ
  have hk : 0 < k := hY.trans_le hkY
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  exact (log_reductionModulus_le k d hdk).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsumR hlogk))

end Erdos345
