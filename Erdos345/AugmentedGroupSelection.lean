import Erdos345.AuxiliaryPairs

namespace Erdos345

/-- Conditional on the precise cosine existence input, the complete
sampling and reserve-allocation construction yields 128 disjoint base
sets with many actual subset sums and a common small span. -/
theorem good_degrees_augmented_groups
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧ 2048 * k ≤ fourierN k ∧
      ∃ H : Fin 128 → Finset ℕ,
        (∀ j, H j ⊆ Finset.Icc 1 (fourierN k)) ∧
        (∀ i j, i ≠ j → Disjoint (H i) (H j)) ∧
        (∀ j, Disjoint (H j) (Finset.Icc 2 257)) ∧
        (∀ j, (reserveGroupSize (fourierN k) k : ℝ) * (fourierN k : ℝ) ^ k / 16 ≤
          (finitePowerSums (H j) k).card) ∧
        (∀ j, (∑ n ∈ H j, (n : ℝ) ^ k) <
          (4 : ℝ) / 3 * (reserveGroupSize (fourierN k) k : ℝ) * (fourierN k : ℝ) ^ k) := by
  classical
  obtain ⟨K, hK⟩ := good_degrees_reserved_groups hinput
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hk20, hlarge, G, hGsub, hGdisj, hGspan, hgood⟩ := hK Y hY
  obtain ⟨B, hBsub, hBcard, hBdisj, hBgood⟩ := reserved_good_allocation (fourierN k) k G hgood
  have hcross (i j : Fin 128) : Disjoint (G i) (B j) :=
    (reservedBases_disjoint (fourierN k) k).symm.mono (hGsub i) (hBsub j)
  refine ⟨k, hkY, hk2Y, hk20, hlarge, (fun j => G j ∪ B j), ?_, ?_, ?_, ?_, ?_⟩
  · intro j n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · have h := (mem_unreservedPopulation (fourierN k) k n).mp (hGsub j hn)
      apply Finset.mem_Icc.mpr
      exact ⟨by omega, h.1.trans (Nat.sub_le _ _)⟩
    · have h := reservedBases_positive (fourierN k) k n (hBsub j hn)
      exact Finset.mem_Icc.mpr ⟨h.1, h.2⟩
  · intro i j hij
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hGdisj i j hij, hcross i j⟩, ⟨(hcross j i).symm, hBdisj i j hij⟩⟩
  · intro j
    apply Finset.disjoint_left.mpr
    intro n hn ha
    rcases Finset.mem_union.mp hn with hn | hn
    · exact (Finset.mem_sdiff.mp (hGsub j hn)).2 ha
    · exact (Finset.disjoint_left.mp (reservedBases_auxiliary_disjoint
        (fourierN k) k hk20 hlarge)) (hBsub j hn) ha
  · intro j
    have h := reserved_augmentation_card_lower (fourierN k) k (G j) (B j)
      hk20 (hBsub j) (hcross j j) (hBgood j)
    simpa only [hBcard] using h
  · intro j
    exact reserved_augmentation_span_upper (fourierN k) k (G j) (B j)
      (by omega) hlarge (hcross j j) (hBsub j) (hBcard j) (hGspan j)

end Erdos345
