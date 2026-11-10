import Erdos345.ShiftAction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

namespace Erdos345

open Finset Polynomial

theorem weighted_sum_square_le {ι : Type*} (S : Finset ι) (w e : ι → ℝ) :
    (∑ i ∈ S, w i * e i) ^ 2 ≤
      (∑ i ∈ S, |w i|) * ∑ i ∈ S, |w i| * e i ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i _ => abs_nonneg (w i))
    (fun i _ => mul_nonneg (abs_nonneg (w i)) (sq_nonneg (e i)))
  intro i _
  rw [mul_pow, ← sq_abs (w i)]
  ring_nf
  exact le_rfl

theorem shifted_nonnegative_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {T X h : ℕ} (hTX : T + h ≤ X) :
    (∑ n ∈ range T, f (n + h)) ≤ ∑ n ∈ range X, f n := by
  classical
  let S := (range T).image (fun n => n + h)
  have hsub : S ⊆ range X := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    apply mem_range.mpr
    have := mem_range.mp hj
    omega
  calc
    (∑ n ∈ range T, f (n + h)) = ∑ n ∈ S, f n := by
      rw [show S = (range T).image (fun n => n + h) from rfl, sum_image]
      intro a _ b _ hab
      exact Nat.add_right_cancel hab
    _ ≤ ∑ n ∈ range X, f n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- A finite Young inequality with every legal input index exposed. -/
theorem convolution_energy_le (w e : ℕ → ℝ) (D T X : ℕ) (hTX : T + D ≤ X) :
    (∑ n ∈ range T, (∑ h ∈ range (D + 1), w h * e (n + h)) ^ 2) ≤
      (∑ h ∈ range (D + 1), |w h|) ^ 2 * ∑ n ∈ range X, e n ^ 2 := by
  let W := ∑ h ∈ range (D + 1), |w h|
  have hW : 0 ≤ W := sum_nonneg (fun h _ => abs_nonneg (w h))
  calc
    (∑ n ∈ range T, (∑ h ∈ range (D + 1), w h * e (n + h)) ^ 2) ≤
        ∑ n ∈ range T, W * ∑ h ∈ range (D + 1), |w h| * e (n + h) ^ 2 := by
      apply sum_le_sum
      intro n _
      exact weighted_sum_square_le _ _ _
    _ = W * ∑ h ∈ range (D + 1), |w h| * ∑ n ∈ range T, e (n + h) ^ 2 := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro h _
      rw [mul_sum]
    _ ≤ W * ∑ h ∈ range (D + 1), |w h| * ∑ n ∈ range X, e n ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact shifted_nonnegative_sum_le (fun n => e n ^ 2) (fun n => sq_nonneg _)
        (by have := mem_range.mp hh; omega)
    _ = _ := by rw [← sum_mul]; dsimp only [W]; ring

theorem integer_nonzero_count_le_energy (r : ℕ → ℤ) (T : ℕ) :
    (((range T).filter (fun n => r n ≠ 0)).card : ℝ) ≤
      ∑ n ∈ range T, (r n : ℝ) ^ 2 := by
  classical
  let B := (range T).filter (fun n => r n ≠ 0)
  calc
    (B.card : ℝ) = ∑ _n ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ B, (r n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hr : r n ≠ 0 := (mem_filter.mp hn).2
      have hs : (1 : ℤ) ≤ r n ^ 2 := by
        have := sq_pos_of_ne_zero hr
        omega
      exact_mod_cast hs
    _ ≤ ∑ n ∈ range T, (r n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => sq_nonneg _)

noncomputable def coefficientL1 (p : ℤ[X]) : ℝ :=
  ∑ h ∈ range (p.natDegree + 1), |(p.coeff h : ℝ)|

theorem coefficientL1_nonneg (p : ℤ[X]) : 0 ≤ coefficientL1 p :=
  sum_nonneg (fun _ _ => abs_nonneg _)

theorem shiftAction_error (p : ℤ[X]) (f : ℕ → ℝ) (m : ℕ → ℤ) (n : ℕ)
    (han : shiftAction (p.map (Int.castRingHom ℝ)) f n = 0) :
    shiftAction (p.map (Int.castRingHom ℝ)) (fun j => f j - (m j : ℝ)) n =
      -(shiftAction p m n : ℝ) := by
  have heq := congrArg (fun g : ℕ → ℝ => g n)
    ((shiftAction (p.map (Int.castRingHom ℝ))).map_sub f (fun j => (m j : ℝ)))
  change shiftAction (p.map (Int.castRingHom ℝ)) (fun j => f j - (m j : ℝ)) n =
    shiftAction (p.map (Int.castRingHom ℝ)) f n -
      shiftAction (p.map (Int.castRingHom ℝ)) (fun j => (m j : ℝ)) n at heq
  have hmap : shiftAction (p.map (Int.castRingHom ℝ)) (fun j => (m j : ℝ)) n =
      (shiftAction p m n : ℝ) := shiftAction_map (Int.castRingHom ℝ) p m n
  rw [han, hmap, zero_sub] at heq
  exact heq

/-- Integrality converts a bounded rounding error into a bound on the number
of nonzero recurrence residuals. No rounding choice is assumed or hidden. -/
theorem recurrence_residual_count_bound (p : ℤ[X]) (f : ℕ → ℝ) (m : ℕ → ℤ)
    (T X : ℕ) (hTX : T + p.natDegree ≤ X)
    (han : ∀ n < T, shiftAction (p.map (Int.castRingHom ℝ)) f n = 0) :
    (((range T).filter (fun n => shiftAction p m n ≠ 0)).card : ℝ) ≤
      coefficientL1 p ^ 2 * ∑ n ∈ range X, (f n - (m n : ℝ)) ^ 2 := by
  let e := fun n => f n - (m n : ℝ)
  have hres (n : ℕ) (hn : n < T) :
      (shiftAction p m n : ℝ) ^ 2 =
        (∑ h ∈ range (p.natDegree + 1), (p.coeff h : ℝ) * e (n + h)) ^ 2 := by
    have he := shiftAction_error p f m n (han n hn)
    rw [shiftAction_sum_of_degree_lt (p.map (Int.castRingHom ℝ)) _
      ((natDegree_map_le).trans_lt (Nat.lt_succ_self p.natDegree))] at he
    simp only [coeff_map, Int.coe_castRingHom] at he
    have hs := congrArg (fun x : ℝ => x ^ 2) he
    simpa only [neg_sq] using hs.symm
  calc
    (((range T).filter (fun n => shiftAction p m n ≠ 0)).card : ℝ) ≤
        ∑ n ∈ range T, (shiftAction p m n : ℝ) ^ 2 := integer_nonzero_count_le_energy _ _
    _ = ∑ n ∈ range T,
        (∑ h ∈ range (p.natDegree + 1), (p.coeff h : ℝ) * e (n + h)) ^ 2 := by
      apply sum_congr rfl
      intro n hn
      exact hres n (mem_range.mp hn)
    _ ≤ coefficientL1 p ^ 2 * ∑ n ∈ range X, e n ^ 2 :=
      convolution_energy_le _ _ _ _ _ hTX

end Erdos345
