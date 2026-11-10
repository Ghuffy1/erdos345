import Erdos345.ConvolutionEnergy

namespace Erdos345

open Finset Polynomial

/-- Among b+1 disjoint blocks, one avoids a finite set with b elements. -/
theorem exists_block_avoiding (B : Finset ℕ) (T : ℕ) :
    ∃ a : ℕ, a + T / (B.card + 1) ≤ T ∧
      ∀ j < T / (B.card + 1), a + j ∉ B := by
  classical
  let L := T / (B.card + 1)
  by_cases hL : L = 0
  · refine ⟨0, ?_, ?_⟩
    · change 0 + L ≤ T
      omega
    · intro j hj
      change j < L at hj
      omega
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hex : ∃ i ∈ range (B.card + 1), ∀ j < L, i * L + j ∉ B := by
    by_contra h
    push Not at h
    have hsub : range (B.card + 1) ⊆ B.image (fun n => n / L) := by
      intro i hi
      obtain ⟨j, hj, hB⟩ := h i hi
      apply mem_image.mpr
      refine ⟨i * L + j, hB, ?_⟩
      rw [Nat.mul_comm i L, Nat.mul_add_div hLpos,
        Nat.div_eq_of_lt hj, Nat.add_zero]
    have hc := card_le_card hsub
    have hi := card_image_le (s := B) (f := fun n => n / L)
    rw [card_range] at hc
    omega
  obtain ⟨i, hi, hfree⟩ := hex
  refine ⟨i * L, ?_, hfree⟩
  have hi' : i + 1 ≤ B.card + 1 := mem_range.mp hi
  have hm := Nat.mul_le_mul_right L hi'
  have ht := Nat.div_mul_le_self T (B.card + 1)
  change L * (B.card + 1) ≤ T at ht
  change i * L + L ≤ T
  nlinarith

theorem real_div_badcount_lower (T b : ℕ) (E : ℝ) (hb : (b : ℝ) ≤ E) :
    (T : ℝ) / (E + 1) - 1 ≤ ((T / (b + 1) : ℕ) : ℝ) := by
  have hE : 0 < E + 1 := by
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  have hrem := Nat.mod_lt T (by omega : 0 < b + 1)
  have hsplit := Nat.mod_add_div T (b + 1)
  have hTnat : T < (b + 1) * (T / (b + 1) + 1) := by nlinarith
  have hTR : (T : ℝ) < ((b : ℝ) + 1) * (((T / (b + 1) : ℕ) : ℝ) + 1) := by
    exact_mod_cast hTnat
  have hmul : ((b : ℝ) + 1) * (((T / (b + 1) : ℕ) : ℝ) + 1) ≤
      (E + 1) * (((T / (b + 1) : ℕ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdiv : (T : ℝ) / (E + 1) < ((T / (b + 1) : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hE).mpr (by nlinarith)
  linarith

/-- The bound is quantitative even when the guaranteed run has length zero. -/
theorem exists_zero_run_of_badcount (r : ℕ → ℤ) (T : ℕ) (E : ℝ)
    (hB : (((range T).filter (fun n => r n ≠ 0)).card : ℝ) ≤ E) :
    ∃ a L : ℕ, a + L ≤ T ∧ (T : ℝ) / (E + 1) - 1 ≤ (L : ℝ) ∧
      ∀ j < L, r (a + j) = 0 := by
  classical
  let B := (range T).filter (fun n => r n ≠ 0)
  obtain ⟨a, hbound, hfree⟩ := exists_block_avoiding B T
  refine ⟨a, T / (B.card + 1), hbound, real_div_badcount_lower T B.card E hB, ?_⟩
  intro j hj
  by_contra hr
  apply hfree j hj
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hr⟩

theorem exists_zero_run_of_energy (r : ℕ → ℤ) (T : ℕ) (E : ℝ)
    (hE : (∑ n ∈ range T, (r n : ℝ) ^ 2) ≤ E) :
    ∃ a L : ℕ, a + L ≤ T ∧ (T : ℝ) / (E + 1) - 1 ≤ (L : ℝ) ∧
      ∀ j < L, r (a + j) = 0 :=
  exists_zero_run_of_badcount r T E ((integer_nonzero_count_le_energy r T).trans hE)

/-- Exact zero recurrence positions from a finite approximation error bound. -/
theorem exists_recurrence_zero_run (p : ℤ[X]) (f : ℕ → ℝ) (m : ℕ → ℤ)
    (T X : ℕ) (hTX : T + p.natDegree ≤ X)
    (han : ∀ n < T, shiftAction (p.map (Int.castRingHom ℝ)) f n = 0) :
    ∃ a L : ℕ, a + L ≤ T ∧
      (T : ℝ) / (coefficientL1 p ^ 2 * (∑ n ∈ range X, (f n - (m n : ℝ)) ^ 2) + 1) - 1
        ≤ (L : ℝ) ∧
      ∀ j < L, shiftAction p m (a + j) = 0 :=
  exists_zero_run_of_badcount (fun n => shiftAction p m n) T _
    (recurrence_residual_count_bound p f m T X hTX han)

end Erdos345
