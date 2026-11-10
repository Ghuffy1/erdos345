import Erdos345.BelovReciprocalFamily
import Mathlib.Data.Set.Finite.Basic

namespace Erdos345

theorem finite_reciprocal_sublevel {ι : Type*} (Λ : ι → ℝ)
    (hΛ : ∀ a, 0 < Λ a) (hs : Summable (fun a => (Λ a)⁻¹)) (x : ℝ) :
    {a | Λ a ≤ x}.Finite := by
  classical
  by_cases hx : 0 < x
  · let s : Set ι := {a | Λ a ≤ x}
    have hc : Summable (fun _ : s => x⁻¹) := by
      apply (hs.subtype s).of_norm_bounded
      intro a
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
      exact (inv_le_inv₀ hx (hΛ a.val)).mpr a.property
    exact Set.finite_coe_iff.mp (Finite.of_summable_const (inv_pos.mpr hx) hc)
  · apply Set.finite_empty.subset
    intro a ha
    have hp := hΛ a
    have hn : x ≤ 0 := le_of_not_gt hx
    exact False.elim (by change Λ a ≤ x at ha; linarith)

noncomputable def belovCutoff (q : ℕ) (x : ℝ) : Finset (BelovFamilyIndex q) :=
  (finite_reciprocal_sublevel (belovDenominator q) (belovDenominator_pos q)
    (summable_inv_belovDenominator q) x).toFinset

theorem mem_belovCutoff (q : ℕ) (x : ℝ) (a : BelovFamilyIndex q) :
    a ∈ belovCutoff q x ↔ belovDenominator q a ≤ x := by
  simp [belovCutoff]

noncomputable def belovCountingProfile (q : ℕ) (x : ℝ) : ℕ := (belovCutoff q x).card

theorem belovCountingProfile_monotone (q : ℕ) : Monotone (belovCountingProfile q) := by
  intro x y hxy
  apply Finset.card_le_card
  intro a ha
  exact (mem_belovCutoff q y a).mpr (((mem_belovCutoff q x a).mp ha).trans hxy)

theorem belovCountingProfile_zero_below_one (q : ℕ) {x : ℝ} (hx : x < 1) :
    belovCountingProfile q x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := (mem_belovCutoff q x a).mp ha
  have hl := one_le_belovDenominator q a
  linarith

theorem belovCountingProfile_one_pos (q : ℕ) : 1 ≤ belovCountingProfile q 1 := by
  apply Finset.card_pos.mpr
  exact ⟨.inl (), (mem_belovCutoff q 1 (.inl ())).mpr (by rw [belovDenominator_base])⟩

noncomputable def belovProfileMajorant (q N : ℕ) : ℝ :=
  ∑' a : BelovFamilyIndex q, min 1 ((N : ℝ) / belovDenominator q a)

theorem belovProfileTerm_nonneg (q N : ℕ) (a : BelovFamilyIndex q) :
    0 ≤ min 1 ((N : ℝ) / belovDenominator q a) :=
  le_min (by norm_num) (div_nonneg (Nat.cast_nonneg N) (belovDenominator_pos q a).le)

theorem belovProfileMajorant_summable (q N : ℕ) :
    Summable (fun a => min 1 ((N : ℝ) / belovDenominator q a)) := by
  apply ((summable_belovFrequency q).mul_left (N : ℝ)).of_norm_bounded
  intro a
  have hn := belovProfileTerm_nonneg q N a
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    _ ≤ (N : ℝ) / belovDenominator q a := min_le_right _ _
    _ = (N : ℝ) * belovFrequency q a := by rw [div_eq_mul_inv, inv_belovDenominator]

theorem belovProfileMajorant_nonneg (q N : ℕ) : 0 ≤ belovProfileMajorant q N := by
  apply tsum_nonneg
  exact belovProfileTerm_nonneg q N

theorem belovProfileMajorant_monotone (q : ℕ) : Monotone (belovProfileMajorant q) := by
  intro N M hNM
  apply (belovProfileMajorant_summable q N).tsum_le_tsum _ (belovProfileMajorant_summable q M)
  intro a
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ (belovDenominator_pos q a).le
  exact_mod_cast hNM

theorem belovCountingProfile_le_majorant (q N : ℕ) :
    (belovCountingProfile q (N : ℝ) : ℝ) ≤ belovProfileMajorant q N := by
  have hsum := (belovProfileMajorant_summable q N).sum_le_tsum (belovCutoff q N)
    (fun a _ => belovProfileTerm_nonneg q N a)
  have heq : (∑ a ∈ belovCutoff q (N : ℝ), min 1 ((N : ℝ) / belovDenominator q a)) =
      (belovCountingProfile q (N : ℝ) : ℝ) := by
    calc
      _ = ∑ _a ∈ belovCutoff q (N : ℝ), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply min_eq_left
        apply (le_div_iff₀ (belovDenominator_pos q a)).mpr
        simpa using (mem_belovCutoff q (N : ℝ) a).mp ha
      _ = _ := by simp [belovCountingProfile]
  rwa [heq] at hsum

theorem belovProfileMajorant_double (q N : ℕ) :
    belovProfileMajorant q (2 * N) ≤ 2 * belovProfileMajorant q N := by
  have htwice := (belovProfileMajorant_summable q N).mul_left 2
  have hsum : belovProfileMajorant q (2 * N) ≤
      ∑' a, 2 * min 1 ((N : ℝ) / belovDenominator q a) := by
    apply (belovProfileMajorant_summable q (2 * N)).tsum_le_tsum _ htwice
    intro a
    push_cast
    have hm := min_le_min_right (2 * ((N : ℝ) / belovDenominator q a))
      (show (1 : ℝ) ≤ 2 by norm_num)
    have hmin : min (2 : ℝ) (2 * ((N : ℝ) / belovDenominator q a)) =
        2 * min 1 ((N : ℝ) / belovDenominator q a) := by
      symm
      simpa only [mul_one] using mul_min_of_nonneg (1 : ℝ)
        ((N : ℝ) / belovDenominator q a) (by norm_num : (0 : ℝ) ≤ 2)
    rw [hmin] at hm
    simpa only [mul_div_assoc] using hm
  simpa only [tsum_mul_left, belovProfileMajorant] using hsum

end Erdos345
