import Erdos345.IntegerArcCount
import Erdos345.SmallNumeratorGrid
import Erdos345.GridCollisionBound

namespace Erdos345

/-- Once the inverse and center exclusion localize the exceptional set,
only small end numerators need a separate energy estimate. -/
theorem powerCollisionSum_le_integer_localized (R : Finset ℕ) (hR : R.Nonempty)
    (q k t V : ℕ) (hq : 0 < q) (D H Hlow r : ℝ)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hinclusion : lowEnergyGrid q k V H ⊆ commonRationalArcs q 1 r)
    (hsmall : ∀ h ∈ smallNumeratorFrequencies q ⌊(q : ℝ) * r⌋₊,
      Hlow ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) +
      ((2 * ⌊(q : ℝ) * r⌋₊ : ℕ) : ℝ) * Real.exp (-(t : ℝ) * Hlow / R.card) := by
  have hsub : nonzeroFrequencies q ∩ lowEnergyGrid q k V H ⊆
      nonzeroFrequencies q ∩ commonRationalArcs q 1 r := by
    intro h hh
    obtain ⟨hhS, hhE⟩ := Finset.mem_inter.mp hh
    exact Finset.mem_inter.mpr ⟨hhS, hinclusion hhE⟩
  have hcount := (Finset.card_le_card hsub).trans (card_nonzero_integerArcs_le q hq r)
  apply powerCollisionSum_le_exceptional_count R hR q k t V _ D H Hlow hmissing hcount
  intro h hhS hhE
  apply hsmall
  exact nonzero_integerArcs_subset_smallNumerators q hq r
    (Finset.mem_inter.mpr ⟨hhS, hinclusion hhE⟩)

/-- A finite collision bound composed with the proved flat inverse and
primitive-center exclusion. The remaining small-numerator energy and
numerical conditions are stated explicitly. -/
theorem powerCollisionSum_le_integer_inverse (R : Finset ℕ) (hR : R.Nonempty)
    (N : ℕ) (w : ℕ → ℕ) (q k t V W X : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (D H E Hlow : ℝ) (hXV : X ≤ V) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k u b X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E)
    (hr : flatInverseRadius k W H ≤ 1)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hsmall : ∀ h ∈ smallNumeratorFrequencies q ⌊(q : ℝ) * flatInverseRadius k W H⌋₊,
      Hlow ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) +
      ((2 * ⌊(q : ℝ) * flatInverseRadius k W H⌋₊ : ℕ) : ℝ) *
        Real.exp (-(t : ℝ) * Hlow / R.card) := by
  exact powerCollisionSum_le_integer_localized R hR q k t V hq D H Hlow
    (flatInverseRadius k W H) hmissing
    (lowEnergyGrid_subset_integerArcs N w q k V W X hq hw hmass H E hXV hW
      hlarge hsize hcenter hbudget hr) hsmall

end Erdos345
