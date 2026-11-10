import Erdos345.LowEnergyGrid
import Erdos345.DeletedPrefixEnergy
import Erdos345.CollisionSplit

namespace Erdos345

/-- An actual Fourier collision sum is bounded by a bulk term and an
exceptional-grid term. The prefix deletion cost is charged explicitly. -/
theorem powerCollisionSum_le_exceptional_count (R : Finset ℕ) (hR : R.Nonempty)
    (q k t V L : ℕ) (D H Hlow : ℝ)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hcount : (nonzeroFrequencies q ∩ lowEnergyGrid q k V H).card ≤ L)
    (hlow : ∀ h ∈ nonzeroFrequencies q, h ∈ lowEnergyGrid q k V H →
      Hlow ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) +
      (L : ℝ) * Real.exp (-(t : ℝ) * Hlow / R.card) := by
  classical
  let S := nonzeroFrequencies q
  let A := S ∩ lowEnergyGrid q k V H
  let f := fun h n : ℕ => (h : ℝ) / q * (n : ℝ) ^ k
  have hhigh : ∀ h ∈ S \ A, H - D ≤ finiteSineEnergy R (f h) := by
    intro h hh
    obtain ⟨hhS, hhA⟩ := Finset.mem_sdiff.mp hh
    have hhq : h < q := ((mem_nonzeroFrequencies q h).mp hhS).2
    have hnlow : h ∉ lowEnergyGrid q k V H := by
      intro hl
      exact hhA (Finset.mem_inter.mpr ⟨hhS, hl⟩)
    have hprefix : H ≤ sineEnergy (f h) V := by
      by_contra hnot
      have hle : sineEnergy (f h) V ≤ H := le_of_lt (lt_of_not_ge hnot)
      exact hnlow ((mem_lowEnergyGrid q k V h H).mpr ⟨hhq, hle⟩)
    exact populationEnergy_ge_prefix_sub_missing R (f h) V D H hmissing hprefix
  have hlowA : ∀ h ∈ A, Hlow ≤ finiteSineEnergy R (f h) := by
    intro h hh
    obtain ⟨hhS, hhL⟩ := Finset.mem_inter.mp hh
    exact hlow h hhS hhL
  have hs := sum_cosineMean_pow_split R S A hR Finset.inter_subset_left f t (H - D)
    Hlow hhigh hlowA
  have hScard : (S.card : ℝ) ≤ q := by exact_mod_cast card_nonzeroFrequencies_le q
  have hAcard : (A.card : ℝ) ≤ L := by
    exact_mod_cast hcount
  have hbounds := add_le_add
    (mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg (-(t : ℝ) * (H - D) / R.card)))
    (mul_le_mul_of_nonneg_right hAcard (Real.exp_nonneg (-(t : ℝ) * Hlow / R.card)))
  exact hs.trans hbounds

theorem powerCollisionSum_le_grid_count (R : Finset ℕ) (hR : R.Nonempty)
    (q k t V L : ℕ) (D H Hlow : ℝ)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hcount : (lowEnergyGrid q k V H).card ≤ L)
    (hlow : ∀ h ∈ nonzeroFrequencies q, h ∈ lowEnergyGrid q k V H →
      Hlow ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) +
      (L : ℝ) * Real.exp (-(t : ℝ) * Hlow / R.card) := by
  exact powerCollisionSum_le_exceptional_count R hR q k t V L D H Hlow hmissing
    ((Finset.card_le_card Finset.inter_subset_right).trans hcount) hlow

theorem powerCollisionSum_le_flat_grid (R : Finset ℕ) (hR : R.Nonempty)
    (N : ℕ) (w : ℕ → ℕ) (q k t V W : ℕ) (hq : 0 < q)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (D H Hlow : ℝ) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hr : flatInverseRadius k W H ≤ 1)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hlow : ∀ h ∈ nonzeroFrequencies q, h ∈ lowEnergyGrid q k V H →
      Hlow ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    powerCollisionSum R k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) +
      (((3 * (k.factorial * normalizedMoment N w) + 1) *
        (⌈2 * (q : ℝ) * flatInverseRadius k W H⌉₊ + 1) : ℕ) : ℝ) *
          Real.exp (-(t : ℝ) * Hlow / R.card) := by
  exact powerCollisionSum_le_grid_count R hR q k t V _ D H Hlow hmissing
    (card_lowEnergyGrid_le N w q k V W hq hw hmass H hW hlarge hsize hr) hlow

end Erdos345
