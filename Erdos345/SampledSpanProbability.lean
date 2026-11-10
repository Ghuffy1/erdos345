import Erdos345.SampledSpanMoments
import Erdos345.FiniteEventBounds

namespace Erdos345

theorem span_variance_ratio (N k M : ℕ) (hN : 0 < N) (hk : 0 < k) (hM : 0 < M) :
    ((N : ℝ) ^ (2 * k + 1) / M) / ((N : ℝ) ^ (k + 1) / ((M : ℝ) * k)) ^ 2 =
      (M : ℝ) * (k : ℝ) ^ 2 / N := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hp : (N : ℝ) ^ (2 * k + 1) = ((N : ℝ) ^ k) ^ 2 * N := by
    rw [show 2 * k + 1 = k * 2 + 1 by omega, pow_add, pow_mul, pow_one]
  rw [hp, pow_succ]
  field_simp
  ring

/-- Chebyshev for the actual labelled group span. The first and second
moments are computed on the same finite product sample space. -/
theorem mean_large_span_le (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : unreservedPopulation N k → Fin M => eventIndicator
      (4 * ((N : ℝ) ^ (k + 1) / ((M : ℝ) * k)) ≤
        sampledPowerSum (unreservedPopulation N k) k ω j)) ≤
          (M : ℝ) * (k : ℝ) ^ 2 / N := by
  have hN : 0 < N := hk.trans_le hkN
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  let A := (N : ℝ) ^ (k + 1) / ((M : ℝ) * k)
  let μ := (1 / (M : ℝ)) * ∑ n ∈ unreservedPopulation N k, (n : ℝ) ^ k
  have hA : 0 < A := by dsimp only [A]; positivity
  have hμ : μ ≤ A := unreserved_span_mean_le N k hk hkN j
  have hpoint : ∀ ω : unreservedPopulation N k → Fin M,
      4 * A ≤ sampledPowerSum (unreservedPopulation N k) k ω j →
      A ^ 2 ≤ (sampledPowerSum (unreservedPopulation N k) k ω j - μ) ^ 2 := by
    intro ω hω
    have hdiff : A ≤ sampledPowerSum (unreservedPopulation N k) k ω j - μ := by linarith
    exact pow_le_pow_left₀ hA.le hdiff 2
  have hmark := uniformMean_event_le
    (fun ω : unreservedPopulation N k → Fin M => (sampledPowerSum (unreservedPopulation N k) k ω j - μ) ^ 2)
    (fun ω => 4 * A ≤ sampledPowerSum (unreservedPopulation N k) k ω j)
    (A ^ 2) (by positivity) (fun _ => sq_nonneg _) hpoint
  have hvar := unreserved_span_variance_le N k hk hkN j
  have hdiv := div_le_div_of_nonneg_right hvar (sq_nonneg A)
  have hratio := span_variance_ratio N k M hN hk hM
  exact hmark.trans (hdiv.trans_eq hratio)

end Erdos345
