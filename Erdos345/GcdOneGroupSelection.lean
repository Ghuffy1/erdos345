import Erdos345.AugmentedGroupSelection

namespace Erdos345

/-- Actual disjoint base sets for the remaining interval step. This is
conditional only on the displayed cosine existence theorem, and does
not itself assert Lev's interval theorem or the original problem. -/
theorem good_degrees_gcd_one_groups
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧ 2048 * k ≤ fourierN k ∧
      ∃ J : Fin 128 → Finset ℕ,
        (∀ j, J j ⊆ Finset.Icc 1 (fourierN k)) ∧
        (∀ i j, i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ j, (reserveGroupSize (fourierN k) k : ℝ) * (fourierN k : ℝ) ^ k / 16 ≤
          (finitePowerSums (J j) k).card) ∧
        (∀ j, (∑ n ∈ J j, (n : ℝ) ^ k) <
          2 * (reserveGroupSize (fourierN k) k : ℝ) * (fourierN k : ℝ) ^ k) ∧
        (∀ (j : Fin 128) (d a : ℕ),
          (∀ n ∈ finitePowerSums (J j) k, n % d = a % d) → d = 1) := by
  classical
  obtain ⟨K, hK⟩ := good_degrees_augmented_groups hinput
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hk20, hlarge, H, hsub, hdisj, havoid, hcard, hspan⟩ := hK Y hY
  have hcross (i j : Fin 128) : Disjoint (H i) (auxiliaryPair j) :=
    (havoid i).mono_right (auxiliaryPair_subset j)
  have hN : 514 ≤ fourierN k := by omega
  have hs : 1 ≤ reserveGroupSize (fourierN k) k := by
    unfold reserveGroupSize
    apply (Nat.le_div_iff_mul_le (show 0 < 512 * k by omega)).mpr
    omega
  refine ⟨k, hkY, hk2Y, hk20, hlarge, (fun j => H j ∪ auxiliaryPair j), ?_, ?_, ?_, ?_, ?_⟩
  · intro j n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hsub j hn
    · have hp := Finset.mem_Icc.mp (auxiliaryPair_subset j hn)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i j hij
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hdisj i j hij, hcross i j⟩, ⟨(hcross j i).symm, auxiliaryPair_disjoint i j hij⟩⟩
  · intro j
    have hc : ((finitePowerSums (H j) k).card : ℝ) ≤
        (finitePowerSums (H j ∪ auxiliaryPair j) k).card := by
      exact_mod_cast Finset.card_le_card (finitePowerSums_mono
        (show H j ⊆ H j ∪ auxiliaryPair j from Finset.subset_union_left) k)
    exact (hcard j).trans hc
  · intro j
    rw [Finset.sum_union (hcross j j)]
    have ha := auxiliaryPair_span_le (fourierN k) k j (by omega) hN
    have hsR : (1 : ℝ) ≤ reserveGroupSize (fourierN k) k := by exact_mod_cast hs
    have hmul := mul_le_mul_of_nonneg_right hsR
      (show (0 : ℝ) ≤ (fourierN k : ℝ) ^ k by positivity)
    have hh := hspan j
    have ht : (0 : ℝ) ≤ (reserveGroupSize (fourierN k) k : ℝ) * (fourierN k : ℝ) ^ k := by
      positivity
    linarith
  · intro j d a h
    exact auxiliaryPair_no_proper_progression (H j) j k d a h

end Erdos345
