import Erdos345.ChebyshevSampling

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

theorem matrix_sum_re_ge_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → I → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hG : ∀ i j, i ≠ j → ‖G i j‖ ≤ E) :
    (∑ i, (G i i).re) - (Fintype.card I : ℝ) ^ 2 * E ≤
      ∑ i, ∑ j, (G i j).re := by
  have hterm (i j : I) : (if i = j then (G i i).re else 0) - E ≤ (G i j).re := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      linarith
    · rw [ite_eq_right hij, zero_sub]
      exact (abs_le.mp ((abs_re_le_norm (G i j)).trans (hG i j hij))).1
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    sum_le_sum (s := (univ : Finset I)) (fun j _ => hterm i j))
  have heq : (∑ i, ∑ j, ((if i = j then (G i i).re else 0) - E)) =
      (∑ i, (G i i).re) - (Fintype.card I : ℝ) ^ 2 * E := by
    simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
    ring
  rwa [heq] at hsum

theorem discreteGram_self_re {I A : Type*} (S : Finset A) (v : I → A → ℂ) (i : I) :
    (discreteGram S v i i).re = ∑ n ∈ S, ‖v i n‖ ^ 2 := by
  rw [discreteGram, re_sum]
  apply sum_congr rfl
  intro n _
  exact (complex_sq_norm_re _).symm

theorem discrete_sum_energy_ge_diagonal {I A : Type*} [Fintype I] [DecidableEq I]
    (S : Finset A) (v : I → A → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hG : ∀ i j, i ≠ j → ‖discreteGram S v i j‖ ≤ E) :
    (∑ i, ∑ n ∈ S, ‖v i n‖ ^ 2) - (Fintype.card I : ℝ) ^ 2 * E ≤
      ∑ n ∈ S, ‖∑ i, v i n‖ ^ 2 := by
  have heq := discrete_energy_gram_identity S v (fun _ => (1 : ℂ))
  simp only [one_mul, map_one] at heq
  rw [heq]
  have h := matrix_sum_re_ge_diagonal (discreteGram S v) E hE hG
  simpa only [discreteGram_self_re] using h

end Erdos345
