import Erdos345.LabelMoments

namespace Erdos345

theorem uniformMean_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω => c * f ω) = c * uniformMean f := by
  simpa only [mul_comm] using uniformMean_mul_const f c

noncomputable def labelWeightSum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (ω : ι → Fin M) (j : Fin M) : ℝ := ∑ i ∈ labelGroup ω j, a i

theorem labelWeightSum_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (ω : ι → Fin M) (j : Fin M) :
    labelWeightSum a ω j = ∑ i, a i * labelHit j (ω i) := by
  simp only [labelWeightSum, labelGroup, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ω i = j <;> simp [labelHit, hi]

theorem mean_labelWeightSum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (j : Fin M) :
    uniformMean (fun ω : ι → Fin M => labelWeightSum a ω j) = (1 / (M : ℝ)) * ∑ i, a i := by
  let _ : Nonempty (Fin M) := ⟨j⟩
  simp only [labelWeightSum_eq, uniformMean_sum, uniformMean_const_mul,
    uniformMean_pi_eval, mean_labelHit]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem centered_labelWeightSum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (ω : ι → Fin M) (j : Fin M) :
    labelWeightSum a ω j - (1 / (M : ℝ)) * ∑ i, a i =
      ∑ i, a i * centeredLabelHit j (ω i) := by
  rw [labelWeightSum_eq]
  simp only [centeredLabelHit, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

theorem labelWeight_variance {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (j : Fin M) :
    uniformMean (fun ω : ι → Fin M =>
      (labelWeightSum a ω j - (1 / (M : ℝ)) * ∑ i, a i) ^ 2) =
        (1 / (M : ℝ)) * (1 - 1 / (M : ℝ)) * ∑ i, a i ^ 2 := by
  let _ : Nonempty (Fin M) := ⟨j⟩
  have heq : (fun ω : ι → Fin M =>
      (labelWeightSum a ω j - (1 / (M : ℝ)) * ∑ i, a i) ^ 2) =
      (fun ω : ι → Fin M => ∑ i, ∑ l,
        (a i * a l) * (centeredLabelHit j (ω i) * centeredLabelHit j (ω l))) := by
    funext ω
    rw [centered_labelWeightSum, pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [heq]
  simp_rw [uniformMean_sum, uniformMean_const_mul, mean_centeredLabelHit_pair]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem labelWeight_variance_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (a : ι → ℝ) (j : Fin M) :
    uniformMean (fun ω : ι → Fin M =>
      (labelWeightSum a ω j - (1 / (M : ℝ)) * ∑ i, a i) ^ 2) ≤
        (1 / (M : ℝ)) * ∑ i, a i ^ 2 := by
  rw [labelWeight_variance]
  have hp : (1 / (M : ℝ)) * (1 - 1 / (M : ℝ)) ≤ 1 / (M : ℝ) := by nlinarith [sq_nonneg (1 / (M : ℝ))]
  exact mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end Erdos345
