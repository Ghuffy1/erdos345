import Erdos345.LabelWeightVariance
import Erdos345.PowerSumIntegral

namespace Erdos345

noncomputable def sampledPowerSum (R : Finset ℕ) (k : ℕ) {M : ℕ}
    (ω : R → Fin M) (j : Fin M) : ℝ := ∑ n ∈ sampledBases R ω j, (n : ℝ) ^ k

theorem sampledPowerSum_eq (R : Finset ℕ) (k : ℕ) {M : ℕ}
    (ω : R → Fin M) (j : Fin M) :
    sampledPowerSum R k ω j = labelWeightSum (fun i : R => (i.val : ℝ) ^ k) ω j := by
  apply Finset.sum_image
  intro i _ v _ hiv
  exact Subtype.ext hiv

theorem mean_sampledPowerSum (R : Finset ℕ) (k : ℕ) {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : R → Fin M => sampledPowerSum R k ω j) =
      (1 / (M : ℝ)) * ∑ n ∈ R, (n : ℝ) ^ k := by
  simp only [sampledPowerSum_eq, mean_labelWeightSum]
  have hs : (∑ i : R, (i.val : ℝ) ^ k) = ∑ n ∈ R, (n : ℝ) ^ k :=
    Finset.sum_coe_sort R (fun n : ℕ => (n : ℝ) ^ k)
  rw [hs]

theorem sampledPowerSum_variance_le (R : Finset ℕ) (k : ℕ) {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : R → Fin M =>
      (sampledPowerSum R k ω j - (1 / (M : ℝ)) * ∑ n ∈ R, (n : ℝ) ^ k) ^ 2) ≤
        (1 / (M : ℝ)) * ∑ n ∈ R, ((n : ℝ) ^ k) ^ 2 := by
  have h := labelWeight_variance_le (fun i : R => (i.val : ℝ) ^ k) j
  have hs : (∑ i : R, (i.val : ℝ) ^ k) = ∑ n ∈ R, (n : ℝ) ^ k :=
    Finset.sum_coe_sort R (fun n : ℕ => (n : ℝ) ^ k)
  have hs2 : (∑ i : R, ((i.val : ℝ) ^ k) ^ 2) = ∑ n ∈ R, ((n : ℝ) ^ k) ^ 2 :=
    Finset.sum_coe_sort R (fun n : ℕ => ((n : ℝ) ^ k) ^ 2)
  simpa only [sampledPowerSum_eq, hs, hs2] using h

theorem unreserved_span_mean_le (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    {M : ℕ} (j : Fin M) :
    (1 / (M : ℝ)) * (∑ n ∈ unreservedPopulation N k, (n : ℝ) ^ k) ≤
      (N : ℝ) ^ (k + 1) / ((M : ℝ) * k) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum := unreserved_power_sum_bound N k hk hkN k
  calc
    _ ≤ (1 / (M : ℝ)) * ((N : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ) ^ (k + 1) / ((M : ℝ) * ((k + 1 : ℕ) : ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; nlinarith)

theorem unreserved_span_variance_le (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : unreservedPopulation N k → Fin M =>
      (sampledPowerSum (unreservedPopulation N k) k ω j -
        (1 / (M : ℝ)) * ∑ n ∈ unreservedPopulation N k, (n : ℝ) ^ k) ^ 2) ≤
          (N : ℝ) ^ (2 * k + 1) / M := by
  have h := sampledPowerSum_variance_le (unreservedPopulation N k) k j
  have hb := mul_le_mul_of_nonneg_left (unreserved_power_square_sum_bound N k hk hkN)
    (show 0 ≤ 1 / (M : ℝ) by positivity)
  exact h.trans (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hb)

end Erdos345
