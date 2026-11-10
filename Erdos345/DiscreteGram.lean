import Erdos345.ConvolutionEnergy
import Mathlib.Analysis.Complex.Basic

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

noncomputable def discreteGram {I A : Type*} (S : Finset A)
    (v : I → A → ℂ) (i j : I) : ℂ :=
  ∑ n ∈ S, conj (v i n) * v j n

theorem complex_sq_norm_re (z : ℂ) : ‖z‖ ^ 2 = (conj z * z).re := by
  rw [Complex.conj_mul']
  simp only [← ofReal_pow, ofReal_re]

theorem discrete_energy_gram_identity {I A : Type*} [Fintype I]
    (S : Finset A) (v : I → A → ℂ) (c : I → ℂ) :
    (∑ n ∈ S, ‖∑ i, c i * v i n‖ ^ 2) =
      ∑ i, ∑ j, (conj (c i) * c j * discreteGram S v i j).re := by
  simp_rw [complex_sq_norm_re, map_sum, map_mul, sum_mul, mul_sum, re_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  unfold discreteGram
  rw [mul_sum, re_sum]
  apply sum_congr rfl
  intro n _
  congr 1
  ring

theorem gram_error_identity {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → I → ℂ) (c : I → ℂ) :
    (∑ i, ∑ j, (conj (c i) * c j * G i j).re) - ∑ i, ‖c i‖ ^ 2 =
      ∑ i, ∑ j, (conj (c i) * c j * (G i j - if i = j then 1 else 0)).re := by
  have hdelta : (∑ i, ∑ j, (conj (c i) * c j * (if i = j then (1 : ℂ) else 0)).re) =
      ∑ i, ‖c i‖ ^ 2 := by
    apply sum_congr rfl
    intro i _
    simp only [mul_one, mul_zero, apply_ite, zero_re]
    rw [sum_ite_eq, ite_eq_left (mem_univ i)]
    exact (complex_sq_norm_re (c i)).symm
  rw [← hdelta, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [mul_sub, sub_re]

theorem gram_error_le {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → I → ℂ) (c : I → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hG : ∀ i j, ‖G i j - if i = j then 1 else 0‖ ≤ ε) :
    |(∑ i, ∑ j, (conj (c i) * c j * G i j).re) - ∑ i, ‖c i‖ ^ 2| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
  rw [gram_error_identity]
  have hsum : (∑ i, ‖c i‖) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    simpa only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, mul_comm] using
      sum_mul_sq_le_sq_mul_sq (univ : Finset I) (fun _ => (1 : ℝ)) (fun i => ‖c i‖)
  calc
    _ ≤ ∑ i, ∑ j, |(conj (c i) * c j * (G i j - if i = j then 1 else 0)).re| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, ε * ‖c i‖ * ‖c j‖ := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ‖conj (c i) * c j * (G i j - if i = j then 1 else 0)‖ := abs_re_le_norm _
        _ = ‖c i‖ * ‖c j‖ * ‖G i j - if i = j then 1 else 0‖ := by
          rw [norm_mul, norm_mul, norm_conj]
        _ ≤ ε * ‖c i‖ * ‖c j‖ := by
          have h := mul_le_mul_of_nonneg_left (hG i j)
            (mul_nonneg (norm_nonneg (c i)) (norm_nonneg (c j)))
          nlinarith
    _ = ε * (∑ i, ‖c i‖) ^ 2 := by
      simp only [← mul_sum, ← sum_mul]
      ring
    _ ≤ ε * (Fintype.card I : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hsum hε
      nlinarith

/-- A finite entrywise Gram estimate gives an energy lower bound without
an unproved spectral assertion or matrix-eigenvalue calculation. -/
theorem discrete_energy_lower_of_gram {I A : Type*} [Fintype I] [DecidableEq I]
    (S : Finset A) (v : I → A → ℂ) (c : I → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hG : ∀ i j, ‖discreteGram S v i j - if i = j then 1 else 0‖ ≤ ε) :
    (1 - ε * (Fintype.card I : ℝ)) * ∑ i, ‖c i‖ ^ 2 ≤
      ∑ n ∈ S, ‖∑ i, c i * v i n‖ ^ 2 := by
  rw [discrete_energy_gram_identity]
  have h := (abs_le.mp (gram_error_le (discreteGram S v) c ε hε hG)).1
  nlinarith

theorem discrete_energy_half_lower_of_gram {I A : Type*} [Fintype I] [DecidableEq I]
    (S : Finset A) (v : I → A → ℂ) (c : I → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε * (Fintype.card I : ℝ) ≤ 1 / 2)
    (hG : ∀ i j, ‖discreteGram S v i j - if i = j then 1 else 0‖ ≤ ε) :
    (∑ i, ‖c i‖ ^ 2) / 2 ≤ ∑ n ∈ S, ‖∑ i, c i * v i n‖ ^ 2 := by
  have h := discrete_energy_lower_of_gram S v c ε hε hG
  have hsum : 0 ≤ ∑ i, ‖c i‖ ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

end Erdos345
