import Erdos345.GridArcCount
import Erdos345.CollisionSplit

namespace Erdos345

def smallNumeratorFrequencies (q A : ℕ) : Finset ℕ :=
  (nonzeroFrequencies q).filter (fun h => min h (q - h) ≤ A)

theorem mem_smallNumeratorFrequencies (q A h : ℕ) :
    h ∈ smallNumeratorFrequencies q A ↔ h ≠ 0 ∧ h < q ∧ min h (q - h) ≤ A := by
  simp only [smallNumeratorFrequencies, Finset.mem_filter, mem_nonzeroFrequencies]
  tauto

theorem card_smallNumeratorFrequencies_le (q A : ℕ) :
    (smallNumeratorFrequencies q A).card ≤ 2 * A := by
  have hsub : smallNumeratorFrequencies q A ⊆
      Finset.Icc 1 A ∪ (Finset.Icc 1 A).image (fun a => q - a) := by
    intro h hh
    obtain ⟨hn, hq, hmin⟩ := (mem_smallNumeratorFrequencies q A h).mp hh
    rcases min_le_iff.mp hmin with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, ha⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨q - h, Finset.mem_Icc.mpr ⟨by omega, hb⟩, by omega⟩
  calc
    _ ≤ (Finset.Icc 1 A ∪ (Finset.Icc 1 A).image (fun a => q - a)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 A).card + ((Finset.Icc 1 A).image (fun a => q - a)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 A).card + (Finset.Icc 1 A).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * A := by simp [Nat.card_Icc]; omega

/-- A nonzero grid frequency close to any integer has a small numerator
on one of the two ends of the grid. -/
theorem near_integer_implies_small_numerator (q h : ℕ) (hq : 0 < q) (hh : h < q)
    (r : ℝ) (z : ℤ) (hnear : |(h : ℝ) / q - z| ≤ r) :
    min h (q - h) ≤ ⌊(q : ℝ) * r⌋₊ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := abs_le.mp hnear
  rcases le_or_gt z 0 with hz | hz
  · have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hs : (h : ℝ) ≤ (q : ℝ) * r := by
      have ht : (h : ℝ) / q ≤ r := by linarith
      have := (div_le_iff₀ hqR).mp ht
      nlinarith
    exact (min_le_left _ _).trans (Nat.le_floor hs)
  · have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
    have hs : ((q - h : ℕ) : ℝ) ≤ (q : ℝ) * r := by
      rw [Nat.cast_sub hh.le]
      have ht : 1 - (h : ℝ) / q ≤ r := by linarith
      have ht' : (q : ℝ) - h ≤ r * q := by
        have := (le_div_iff₀ hqR).mp (show 1 - r ≤ (h : ℝ) / q by linarith)
        nlinarith
      nlinarith
    exact (min_le_right _ _).trans (Nat.le_floor hs)

theorem nonzero_integerArcs_subset_smallNumerators (q : ℕ) (hq : 0 < q) (r : ℝ) :
    nonzeroFrequencies q ∩ commonRationalArcs q 1 r ⊆
      smallNumeratorFrequencies q ⌊(q : ℝ) * r⌋₊ := by
  intro h hh
  obtain ⟨hhS, hhA⟩ := Finset.mem_inter.mp hh
  obtain ⟨hn, hhq⟩ := (mem_nonzeroFrequencies q h).mp hhS
  change h ∈ (centerNumerators 1).biUnion (fun z => gridNear q ((z : ℝ) / (1 : ℕ)) r) at hhA
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hhA
  have hz' : h < q ∧ |(h : ℝ) / q - (z : ℝ) / ((1 : ℕ) : ℝ)| ≤ r :=
    (mem_gridNear q h ((z : ℝ) / ((1 : ℕ) : ℝ)) r).mp hz
  have hnear : |(h : ℝ) / q - (z : ℝ)| ≤ r := by
    simpa only [Nat.cast_one, div_one] using hz'.2
  exact (mem_smallNumeratorFrequencies q _ h).mpr
    ⟨hn, hhq, near_integer_implies_small_numerator q h hq hhq r z hnear⟩

theorem card_nonzero_integerArcs_le (q : ℕ) (hq : 0 < q) (r : ℝ) :
    (nonzeroFrequencies q ∩ commonRationalArcs q 1 r).card ≤ 2 * ⌊(q : ℝ) * r⌋₊ :=
  (Finset.card_le_card (nonzero_integerArcs_subset_smallNumerators q hq r)).trans
    (card_smallNumeratorFrequencies_le q _)

end Erdos345
