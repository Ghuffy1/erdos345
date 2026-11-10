import Erdos345.RootSeparation

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

noncomputable def modulatedSequence (z : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ := a n * z ^ n

theorem modulated_discreteGram (a b : ℕ → ℂ) (x y : ℂ) (L : ℕ) :
    (∑ n ∈ range L, conj (modulatedSequence x a n) * modulatedSequence y b n) =
      ∑ n ∈ range L, (conj (a n) * b n) * (conj x * y) ^ n := by
  apply sum_congr rfl
  intro n _
  simp only [modulatedSequence, map_mul, map_pow, mul_pow]
  ring

theorem modulated_discreteGram_offDiagonal_le
    (a b : ℕ → ℂ) (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (L : ℕ) (hL : 0 < L) (B V δ : ℝ) (hB : 0 ≤ B) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hsep : δ ≤ ‖conj x * y - 1‖)
    (ha : ∀ n < L, ‖a n‖ ≤ B) (hb : ∀ n < L, ‖b n‖ ≤ B)
    (had : ∀ n < L - 1, ‖a (n + 1) - a n‖ ≤ V / L)
    (hbd : ∀ n < L - 1, ‖b (n + 1) - b n‖ ≤ V / L) :
    ‖∑ n ∈ range L, conj (modulatedSequence x a n) * modulatedSequence y b n‖ ≤
      (B ^ 2 + 2 * B * V) * (2 / δ) := by
  rw [modulated_discreteGram]
  have hunit : ‖conj x * y‖ = 1 := by rw [norm_mul, norm_conj, hx, hy, one_mul]
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  apply oscillatory_sum_norm_le_of_step_bound (fun n => conj (a n) * b n)
    (conj x * y) hunit δ hδ hsep L hL (B ^ 2) (2 * B * V) (by positivity)
  · rw [norm_mul, norm_conj]
    exact (mul_le_mul (ha _ (by omega)) (hb _ (by omega)) (norm_nonneg _) hB).trans_eq (pow_two B).symm
  · intro n hn
    have hnL : n < L := by omega
    have hn1L : n + 1 < L := by omega
    have hdiff : ‖conj (a (n + 1)) - conj (a n)‖ ≤ V / L := by
      rw [← map_sub, norm_conj]
      exact had n hn
    calc
      _ ≤ ‖conj (a (n + 1))‖ * ‖b (n + 1) - b n‖ +
          ‖b n‖ * ‖conj (a (n + 1)) - conj (a n)‖ :=
        product_step_norm_le (fun n => conj (a n)) b n
      _ ≤ B * (V / L) + B * (V / L) := by
        apply add_le_add
        · exact mul_le_mul (by rw [norm_conj]; exact ha _ hn1L) (hbd n hn)
            (norm_nonneg _) hB
        · exact mul_le_mul (hb n hnL) hdiff (norm_nonneg _) hB
      _ = (2 * B * V) / L := by ring

theorem cyclotomic_modulated_offDiagonal_le
    (N : ℕ) (i j : CyclotomicRootIndex (Icc 1 N)) (hij : i ≠ j)
    (a b : ℕ → ℂ) (L : ℕ) (hL : 0 < L) (B V : ℝ) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (ha : ∀ n < L, ‖a n‖ ≤ B) (hb : ∀ n < L, ‖b n‖ ≤ B)
    (had : ∀ n < L - 1, ‖a (n + 1) - a n‖ ≤ V / L)
    (hbd : ∀ n < L - 1, ‖b (n + 1) - b n‖ ≤ V / L) :
    ‖∑ n ∈ range L,
      conj (modulatedSequence (cyclotomicRootValue i) a n) *
        modulatedSequence (cyclotomicRootValue j) b n‖ ≤
      2 * (N : ℝ) ^ 2 * (B ^ 2 + 2 * B * V) := by
  have hi := isPrimitiveRoot_of_mem_primitiveRoots i.2.property
  have hj := isPrimitiveRoot_of_mem_primitiveRoots j.2.property
  have hiPos : 0 < (i.1 : ℕ) := (mem_Icc.mp i.1.property).1
  have hjPos : 0 < (j.1 : ℕ) := (mem_Icc.mp j.1.property).1
  have hN : (0 : ℝ) < N := by
    exact_mod_cast hiPos.trans_le (mem_Icc.mp i.1.property).2
  have h := modulated_discreteGram_offDiagonal_le a b _ _
    ((hi.isOfFinOrder (Nat.ne_of_gt hiPos)).norm_eq_one)
    ((hj.isOfFinOrder (Nat.ne_of_gt hjPos)).norm_eq_one) L hL B V (1 / (N : ℝ) ^ 2)
    hB hV (by positivity) (cyclotomic_root_separation N i j hij) ha hb had hbd
  change ‖∑ n ∈ range L,
    conj (modulatedSequence (cyclotomicRootValue i) a n) *
      modulatedSequence (cyclotomicRootValue j) b n‖ ≤ _ at h
  calc
    _ ≤ (B ^ 2 + 2 * B * V) * (2 / (1 / (N : ℝ) ^ 2)) := h
    _ = _ := by field_simp

end Erdos345
