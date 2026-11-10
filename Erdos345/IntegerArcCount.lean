import Erdos345.LowEnergyGrid
import Erdos345.NonintegerCenterExclusion

namespace Erdos345

/-- After primitive-center exclusion, the low-energy grid lies near
integers. There are only four relevant integer centers for radius <=1. -/
theorem lowEnergyGrid_subset_integerArcs (N : ℕ) (w : ℕ → ℕ)
    (q k V W X : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (H E : ℝ) (hXV : X ≤ V) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k u b X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E)
    (hr : flatInverseRadius k W H ≤ 1) :
    lowEnergyGrid q k V H ⊆ commonRationalArcs q 1 (flatInverseRadius k W H) := by
  intro h hh
  obtain ⟨hhq, hhE⟩ := (mem_lowEnergyGrid q k V h H).mp hh
  obtain ⟨z, hz⟩ := flat_inverse_integer_center N w k V W X hw hmass ((h : ℝ) / q)
    H E hhE hXV hW hlarge hsize hcenter hbudget
  exact mem_commonRationalArcs_of_near q 1 h hq (by decide) hhq _ hr z (by simpa using hz)

theorem card_lowEnergyGrid_integer_le (N : ℕ) (w : ℕ → ℕ)
    (q k V W X : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (H E : ℝ) (hXV : X ≤ V) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k u b X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E)
    (hr : flatInverseRadius k W H ≤ 1) :
    (lowEnergyGrid q k V H).card ≤ 4 * (⌈2 * (q : ℝ) * flatInverseRadius k W H⌉₊ + 1) := by
  have hs := lowEnergyGrid_subset_integerArcs N w q k V W X hq hw hmass H E
    hXV hW hlarge hsize hcenter hbudget hr
  simpa only [Nat.mul_one, Nat.reduceAdd] using
    (Finset.card_le_card hs).trans (card_commonRationalArcs_le q 1 hq (flatInverseRadius k W H))

end Erdos345
