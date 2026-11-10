import Erdos345.BelovPrimeMass

namespace Erdos345

noncomputable def belovProfileLevel (q N j : ℕ) : ℝ :=
  ∑ a : DyadicLevelIndex (belovLevelPrimes q) belovMultiplicity j,
    min 1 ((N : ℝ) * dyadicFrequency (belovLevelPrimes q) belovMultiplicity ⟨j, a⟩)

theorem summable_belovProfileAtoms (q N : ℕ) :
    Summable (fun a : DyadicSineIndex (belovLevelPrimes q) belovMultiplicity =>
      min 1 ((N : ℝ) * dyadicFrequency (belovLevelPrimes q) belovMultiplicity a)) := by
  have h := (belovProfileMajorant_summable q N).comp_injective
    (Sum.inr_injective (α := Unit) (β := DyadicSineIndex (belovLevelPrimes q) belovMultiplicity))
  change Summable (fun a : DyadicSineIndex (belovLevelPrimes q) belovMultiplicity =>
    min 1 ((N : ℝ) / (dyadicFrequency (belovLevelPrimes q) belovMultiplicity a)⁻¹)) at h
  simpa only [div_eq_mul_inv, inv_inv] using h

theorem belovProfileLevel_nonneg (q N j : ℕ) : 0 ≤ belovProfileLevel q N j := by
  apply Finset.sum_nonneg
  intro a _
  exact le_min (by norm_num) (mul_nonneg (Nat.cast_nonneg N)
    (dyadicAtomFrequency_nonneg j a.1 a.2))

theorem summable_belovProfileLevels (q N : ℕ) : Summable (belovProfileLevel q N) := by
  have h := (summable_sigma_of_nonneg
    (f := fun a : DyadicSineIndex (belovLevelPrimes q) belovMultiplicity =>
      min 1 ((N : ℝ) * dyadicFrequency (belovLevelPrimes q) belovMultiplicity a))
    (fun a => le_min (by norm_num) (mul_nonneg (Nat.cast_nonneg N)
      (dyadicAtomFrequency_nonneg a.1 a.2.1 a.2.2)))).mp (summable_belovProfileAtoms q N)
  change Summable (fun j => ∑ a : DyadicLevelIndex (belovLevelPrimes q) belovMultiplicity j,
    min 1 ((N : ℝ) * dyadicFrequency (belovLevelPrimes q) belovMultiplicity ⟨j, a⟩))
  simpa only [tsum_fintype] using h.2

theorem belovProfileMajorant_eq_levels (q N : ℕ) :
    belovProfileMajorant q N = min 1 (N : ℝ) + ∑' j, belovProfileLevel q N j := by
  have hl : Summable ((fun a : BelovFamilyIndex q =>
      min 1 ((N : ℝ) / belovDenominator q a)) ∘ Sum.inl) := Summable.of_finite
  have hr : Summable ((fun a : BelovFamilyIndex q =>
      min 1 ((N : ℝ) / belovDenominator q a)) ∘ Sum.inr) :=
    (belovProfileMajorant_summable q N).comp_injective Sum.inr_injective
  unfold belovProfileMajorant
  rw [Summable.tsum_sum hl hr]
  simp only [belovDenominator, belovFrequency, inv_one, div_one, tsum_fintype, Fintype.sum_unique]
  simp_rw [div_eq_mul_inv, inv_inv]
  rw [(summable_belovProfileAtoms q N).tsum_sigma]
  simp only [tsum_fintype, belovProfileLevel]

theorem belovProfileLevel_le_count (q N j : ℕ) (hq : 256 ≤ q) :
    belovProfileLevel q N j ≤ (5 / 2 : ℝ) * (q : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 4 := by
  have hb : belovProfileLevel q N j ≤
      ∑ a : DyadicLevelIndex (belovLevelPrimes q) belovMultiplicity j, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro a _
    exact min_le_left _ _
  have heq : (∑ a : DyadicLevelIndex (belovLevelPrimes q) belovMultiplicity j, (1 : ℝ)) =
      (belovMultiplicity j : ℝ) * (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul]
    rw [← Finset.sum_mul]
    rw [mul_comm]
    congr 1
    exact Finset.sum_finset_coe (fun p : ℕ => (p : ℝ)) (belovLevelPrimes q j)
  exact (hb.trans_eq heq).trans (belov_level_count_bound q j hq)

theorem belovProfileLevel_le_reciprocal (q N j : ℕ) (hq : 256 ≤ q) :
    belovProfileLevel q N j ≤
      (5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 5 / 2 ^ (j + 1) := by
  have hb : belovProfileLevel q N j ≤ (N : ℝ) *
      (∑ a : DyadicLevelIndex (belovLevelPrimes q) belovMultiplicity j,
        dyadicFrequency (belovLevelPrimes q) belovMultiplicity ⟨j, a⟩) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    exact min_le_right _ _
  rw [sum_dyadicFrequency_level (belovLevelPrimes q) belovMultiplicity j
    (fun p hp => (Finset.mem_Icc.mp (belovLevelPrimes_subset q j hp)).1)] at hb
  have heq : (∑ p ∈ belovLevelPrimes q j, (p : ℝ) * (belovMultiplicity j : ℝ) ^ 2 / 2 ^ (j + 1)) =
      (belovMultiplicity j : ℝ) ^ 2 * (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) / 2 ^ (j + 1) := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
    ring
  rw [heq] at hb
  have ht := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (belov_level_reciprocal_numerator_bound q j hq) (show (0 : ℝ) ≤ 2 ^ (j + 1) by positivity))
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  exact hb.trans (by convert ht using 1; ring)

end Erdos345
