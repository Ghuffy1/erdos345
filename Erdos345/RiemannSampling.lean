import Erdos345.UniformChebyshevEnergy

namespace Erdos345

open Finset MeasureTheory intervalIntegral

theorem uniform_cell_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f)
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖f x - f y‖ ≤ K * |x - y|)
    (L n : ℕ) (hL : 0 < L) (hn : n < L) :
    ‖(1 / (L : ℝ)) • f ((n : ℝ) / L) -
        ∫ x in ((n : ℝ) / L)..((n + 1 : ℕ) : ℝ) / L, f x‖ ≤ K / (L : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let a : ℝ := (n : ℝ) / L
  let b : ℝ := ((n + 1 : ℕ) : ℝ) / L
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hLR.le
  have hb : b ≤ 1 := (div_le_one hLR).mpr (by exact_mod_cast Nat.succ_le_of_lt hn)
  have hab : a ≤ b := div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hLR.le
  have hwidth : b - a = 1 / (L : ℝ) := by dsimp [a, b]; push_cast; ring
  have hcell : ‖∫ x in a..b, f a - f x‖ ≤ (K / L) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hxx : x ∈ Set.Icc a b := (Set.uIoc_of_le hab ▸ hx) |> Set.Ioc_subset_Icc_self
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans hxx.1, hxx.2.trans hb⟩
    have ha01 : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
    have h := hLip a ha01 x hx01
    rw [abs_of_nonpos (sub_nonpos.mpr hxx.1)] at h
    have hdx : -(a - x) ≤ 1 / (L : ℝ) := by linarith [hxx.2]
    have hmul := mul_le_mul_of_nonneg_left hdx hK
    calc
      _ ≤ K * -(a - x) := h
      _ ≤ K * (1 / L) := hmul
      _ = _ := by ring
  have heq : (1 / (L : ℝ)) • f a - (∫ x in a..b, f x) =
      ∫ x in a..b, f a - f x := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, hwidth]
  change ‖(1 / (L : ℝ)) • f a - (∫ x in a..b, f x)‖ ≤ _
  rw [heq]
  calc
    _ ≤ (K / L) * |b - a| := hcell
    _ = K / (L : ℝ) ^ 2 := by rw [hwidth, abs_of_pos (by positivity)]; ring

/-- Explicit left-endpoint quadrature error for a Lipschitz function on
the unit interval, with all sample locations and the sample count fixed. -/
theorem uniform_sampling_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f)
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖f x - f y‖ ≤ K * |x - y|)
    (L : ℕ) (hL : 0 < L) :
    ‖(1 / (L : ℝ)) • (∑ n ∈ range L, f ((n : ℝ) / L)) -
        ∫ x in (0 : ℝ)..1, f x‖ ≤ K / L := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum := sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun n => (n : ℝ) / L) (n := L)
    (fun k _ => hf.intervalIntegrable ((k : ℝ) / L) (((k + 1 : ℕ) : ℝ) / L))
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hLR)] at hsum
  rw [← hsum, Finset.smul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range L,
        ‖(1 / (L : ℝ)) • f ((n : ℝ) / L) -
          ∫ x in ((n : ℝ) / L)..((n + 1 : ℕ) : ℝ) / L, f x‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range L, K / (L : ℝ) ^ 2 :=
      sum_le_sum (fun n hn => uniform_cell_error_le f hf K hK hLip L n hL (mem_range.mp hn))
    _ = K / L := by simp; field_simp

end Erdos345
