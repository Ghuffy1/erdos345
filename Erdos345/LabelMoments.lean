import Erdos345.FiniteCoordinateMean
import Erdos345.LabelSampling

namespace Erdos345

def labelHit {M : ℕ} (j a : Fin M) : ℝ := if a = j then 1 else 0

noncomputable def centeredLabelHit {M : ℕ} (j a : Fin M) : ℝ := labelHit j a - 1 / (M : ℝ)

theorem mean_labelHit {M : ℕ} (j : Fin M) : uniformMean (labelHit j) = 1 / (M : ℝ) := by
  simp [uniformMean, labelHit]

theorem mean_centeredLabelHit {M : ℕ} (j : Fin M) : uniformMean (centeredLabelHit j) = 0 := by
  let _ : Nonempty (Fin M) := ⟨j⟩
  change uniformMean (fun a : Fin M => labelHit j a - (fun _ : Fin M => 1 / (M : ℝ)) a) = 0
  rw [uniformMean_sub, mean_labelHit, uniformMean_const, sub_self]

theorem mean_centeredLabelHit_square {M : ℕ} (j : Fin M) :
    uniformMean (fun a : Fin M => centeredLabelHit j a ^ 2) =
      (1 / (M : ℝ)) * (1 - 1 / (M : ℝ)) := by
  let _ : Nonempty (Fin M) := ⟨j⟩
  have heq : (fun a : Fin M => centeredLabelHit j a ^ 2) =
      (fun a : Fin M => labelHit j a * (1 - 2 / (M : ℝ)) + (1 / (M : ℝ)) ^ 2) := by
    funext a
    by_cases ha : a = j
    · simp only [centeredLabelHit, labelHit, ite_eq_left ha]
      ring
    · simp only [centeredLabelHit, labelHit, ite_eq_right ha, zero_mul, zero_add, zero_sub, neg_sq]
  rw [heq, uniformMean_add, uniformMean_mul_const, mean_labelHit, uniformMean_const]
  ring

theorem mean_centeredLabelHit_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (j : Fin M) (a b : ι) :
    uniformMean (fun ω : ι → Fin M => centeredLabelHit j (ω a) * centeredLabelHit j (ω b)) =
      if a = b then (1 / (M : ℝ)) * (1 - 1 / (M : ℝ)) else 0 := by
  let _ : Nonempty (Fin M) := ⟨j⟩
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    have heq : (fun ω : ι → Fin M => centeredLabelHit j (ω a) * centeredLabelHit j (ω a)) =
        (fun ω : ι → Fin M => centeredLabelHit j (ω a) ^ 2) := by funext ω; ring
    rw [heq, uniformMean_pi_eval a (fun x : Fin M => centeredLabelHit j x ^ 2), mean_centeredLabelHit_square]
  · rw [ite_eq_right hab, uniformMean_pi_two a b hab, mean_centeredLabelHit, mul_zero]

end Erdos345
