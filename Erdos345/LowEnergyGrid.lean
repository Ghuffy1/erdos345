import Erdos345.GridArcCount

namespace Erdos345

noncomputable def lowEnergyGrid (q k V : ℕ) (H : ℝ) : Finset ℕ :=
  (Finset.range q).filter (fun h =>
    sineEnergy (fun n => (h : ℝ) / q * (n : ℝ) ^ k) V ≤ H)

theorem mem_lowEnergyGrid (q k V h : ℕ) (H : ℝ) :
    h ∈ lowEnergyGrid q k V H ↔ h < q ∧
      sineEnergy (fun n => (h : ℝ) / q * (n : ℝ) ^ k) V ≤ H := by
  classical
  simp only [lowEnergyGrid, Finset.mem_filter, Finset.mem_range]

/-- The common-denominator inverse theorem gives an actual inclusion of
all low-energy Fourier grid points in a fixed finite union of arcs. -/
theorem lowEnergyGrid_subset_commonRationalArcs (N : ℕ) (w : ℕ → ℕ)
    (q k V W : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (H : ℝ) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hr : flatInverseRadius k W H ≤ 1) :
    lowEnergyGrid q k V H ⊆
      commonRationalArcs q (k.factorial * normalizedMoment N w) (flatInverseRadius k W H) := by
  intro h hh
  obtain ⟨hhq, hhE⟩ := (mem_lowEnergyGrid q k V h H).mp hh
  obtain ⟨hB, _, u, hnear⟩ := flat_inverse_of_energy_le N w k V W hw hmass
    ((h : ℝ) / q) H hhE hW hlarge hsize
  exact mem_commonRationalArcs_of_near q _ h hq hB hhq _ hr u hnear

theorem card_lowEnergyGrid_le (N : ℕ) (w : ℕ → ℕ) (q k V W : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (H : ℝ) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hr : flatInverseRadius k W H ≤ 1) :
    (lowEnergyGrid q k V H).card ≤ (3 * (k.factorial * normalizedMoment N w) + 1) *
      (⌈2 * (q : ℝ) * flatInverseRadius k W H⌉₊ + 1) := by
  exact (Finset.card_le_card (lowEnergyGrid_subset_commonRationalArcs N w q k V W hq
    hw hmass H hW hlarge hsize hr)).trans (card_commonRationalArcs_le q _ hq _)

end Erdos345
