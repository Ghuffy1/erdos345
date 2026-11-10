import Erdos345.FiniteCoordinateMean
import Erdos345.FiniteEventBounds

namespace Erdos345

noncomputable def finiteRowMean {Ω Α : Type*} (S : Finset Α) (f : Ω → Α → ℝ) (ω : Ω) : ℝ :=
  (∑ a ∈ S, f ω a) / S.card

theorem mean_finiteRowMean {Ω Α : Type*} [Fintype Ω] (S : Finset Α) (f : Ω → Α → ℝ) :
    uniformMean (finiteRowMean S f) = (∑ a ∈ S, uniformMean (fun ω => f ω a)) / S.card := by
  unfold finiteRowMean
  simp only [div_eq_mul_inv]
  rw [uniformMean_mul_const, uniformMean_finset_sum]

theorem finiteRowMean_nonneg {Ω Α : Type*} (S : Finset Α) (f : Ω → Α → ℝ)
    (hf : ∀ ω a, a ∈ S → 0 ≤ f ω a) (ω : Ω) : 0 ≤ finiteRowMean S f ω := by
  exact div_nonneg (Finset.sum_nonneg (fun a ha => hf ω a ha)) (Nat.cast_nonneg _)

theorem mean_finiteRowMean_le {Ω Α : Type*} [Fintype Ω] (S : Finset Α) (hS : S.Nonempty)
    (f : Ω → Α → ℝ) (δ : ℝ) (hf : ∀ a ∈ S, uniformMean (fun ω => f ω a) ≤ δ) :
    uniformMean (finiteRowMean S f) ≤ δ := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  rw [mean_finiteRowMean]
  apply (div_le_iff₀ hcard).mpr
  have h := Finset.sum_le_sum hf
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using h

theorem eventIndicator_sum_card {Α : Type*} (S : Finset Α) (P : Α → Prop) [DecidablePred P] :
    (∑ a ∈ S, eventIndicator (P a)) = ((S.filter P).card : ℝ) := by
  classical
  calc
    _ = ∑ a ∈ S, if P a then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : P a <;> simp [eventIndicator, h]
    _ = _ := Finset.sum_boole P S

theorem complement_filter_half {Α : Type*} (S : Finset Α) (hS : S.Nonempty) (P : Α → Prop) [DecidablePred P]
    (hmean : (∑ a ∈ S, eventIndicator (P a)) / S.card < (1 : ℝ) / 2) :
    (S.card : ℝ) / 2 ≤ ((S.filter (fun a => ¬ P a)).card : ℝ) := by
  classical
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hsum : (∑ a ∈ S, eventIndicator (P a)) +
      (∑ a ∈ S, eventIndicator (¬ P a)) = S.card := by
    rw [← Finset.sum_add_distrib]
    have hp : ∀ a, eventIndicator (P a) + eventIndicator (¬ P a) = 1 := by
      intro a
      by_cases h : P a <;> simp [eventIndicator, h]
    simp only [hp, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [eventIndicator_sum_card] at hsum
  have hmul := (div_lt_iff₀ hcard).mp hmean
  rw [eventIndicator_sum_card] at hmul
  rw [eventIndicator_sum_card] at hsum
  linarith

theorem mean_bad_row_le {Ω Α : Type*} [Fintype Ω] (S : Finset Α) (hS : S.Nonempty)
    (P : Ω → Α → Prop) (δ : ℝ)
    (hP : ∀ a ∈ S, uniformMean (fun ω => eventIndicator (P ω a)) ≤ δ) :
    uniformMean (fun ω => eventIndicator
      ((1 : ℝ) / 2 ≤ finiteRowMean S (fun ω a => eventIndicator (P ω a)) ω)) ≤ 2 * δ := by
  have hm := mean_finiteRowMean_le S hS (fun ω a => eventIndicator (P ω a)) δ hP
  have hmark := uniformMean_event_le
    (finiteRowMean S (fun ω a => eventIndicator (P ω a)))
    (fun ω => (1 : ℝ) / 2 ≤ finiteRowMean S (fun ω a => eventIndicator (P ω a)) ω)
    (1 / 2) (by norm_num)
    (finiteRowMean_nonneg S _ (fun _ _ _ => eventIndicator_nonneg _)) (fun _ h => h)
  linarith

end Erdos345
