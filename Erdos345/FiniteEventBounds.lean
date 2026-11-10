import Erdos345.FiniteExpectation

namespace Erdos345

noncomputable def eventIndicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

theorem eventIndicator_nonneg (P : Prop) : 0 ≤ eventIndicator P := by
  classical
  unfold eventIndicator
  split_ifs <;> norm_num

theorem exists_lt_of_uniformMean_lt {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (a : ℝ) (hmean : uniformMean f < a) : ∃ ω, f ω < a := by
  by_contra h
  push Not at h
  have hm := uniformMean_mono (fun _ : Ω => a) f h
  rw [uniformMean_const] at hm
  linarith

/-- Finite Markov bound for an arbitrary event, proved directly from
the normalized sum over the sample space. -/
theorem uniformMean_event_le {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (P : Ω → Prop)
    (B : ℝ) (hB : 0 < B) (hf : ∀ ω, 0 ≤ f ω)
    (hP : ∀ ω, P ω → B ≤ f ω) :
    uniformMean (fun ω => eventIndicator (P ω)) ≤ uniformMean f / B := by
  classical
  have hpoint : ∀ ω, eventIndicator (P ω) * B ≤ f ω := by
    intro ω
    by_cases h : P ω
    · simpa only [eventIndicator, ite_eq_left h, one_mul] using hP ω h
    · simpa only [eventIndicator, ite_eq_right h, zero_mul] using hf ω
  have hm := uniformMean_mono (fun ω => eventIndicator (P ω) * B) f hpoint
  rw [uniformMean_mul_const] at hm
  exact (le_div_iff₀ hB).mpr hm

/-- A total bad-event probability below one leaves at least one sample
where every event fails. No independence among the events is required. -/
theorem finite_bad_event_selection {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (P : ι → Ω → Prop)
    (hbad : (∑ i, uniformMean (fun ω => eventIndicator (P i ω))) < 1) :
    ∃ ω : Ω, ∀ i, ¬ P i ω := by
  classical
  have hm : uniformMean (fun ω => ∑ i, eventIndicator (P i ω)) < 1 := by
    rw [uniformMean_sum]
    exact hbad
  obtain ⟨ω, hω⟩ := exists_lt_of_uniformMean_lt _ 1 hm
  refine ⟨ω, ?_⟩
  intro i hi
  have hle : eventIndicator (P i ω) ≤ ∑ j, eventIndicator (P j ω) :=
    Finset.single_le_sum (fun j _ => eventIndicator_nonneg (P j ω)) (Finset.mem_univ i)
  have hI : eventIndicator (P i ω) = 1 := by simp only [eventIndicator, ite_eq_left hi]
  rw [hI] at hle
  linarith

end Erdos345
