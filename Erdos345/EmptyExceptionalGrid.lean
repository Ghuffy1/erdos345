import Erdos345.SamplingPopulationEnergy
import Erdos345.IntegerGridCollision

namespace Erdos345

theorem unreservedPopulation_subset_prefix (N k : ℕ) :
    unreservedPopulation N k ⊆ Finset.range (unreservedEndpoint N k + 1) := by
  intro n hn
  apply Finset.mem_range.mpr
  have h := ((mem_unreservedPopulation N k n).mp hn).1
  omega

theorem population_energy_le_prefix (R : Finset ℕ) (V : ℕ) (hR : R ⊆ Finset.range V)
    (f : ℕ → ℝ) : finiteSineEnergy R f ≤ sineEnergy f V :=
  finiteSineEnergy_mono R (Finset.range V) hR f

/-- If every integer-localized exceptional frequency has population
energy greater than the prefix cutoff, the exceptional nonzero grid
is empty. This uses both sides of the prefix/population comparison. -/
theorem nonzero_lowEnergyGrid_empty (R : Finset ℕ) (q k V : ℕ) (hq : 0 < q)
    (H ρ : ℝ) (hR : R ⊆ Finset.range V)
    (hinclusion : lowEnergyGrid q k V H ⊆ commonRationalArcs q 1 ρ)
    (hsmall : ∀ h ∈ smallNumeratorFrequencies q ⌊(q : ℝ) * ρ⌋₊,
      H < finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    nonzeroFrequencies q ∩ lowEnergyGrid q k V H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨hhS, hhE⟩ := Finset.mem_inter.mp hh
  have hhsmall := nonzero_integerArcs_subset_smallNumerators q hq ρ
    (Finset.mem_inter.mpr ⟨hhS, hinclusion hhE⟩)
  have hlow := ((mem_lowEnergyGrid q k V h H).mp hhE).2
  have hle := (population_energy_le_prefix R V hR
    (fun n => (h : ℝ) / q * (n : ℝ) ^ k)).trans hlow
  exact (hsmall h hhsmall).not_ge hle

theorem flatInverseRadius_nonneg (k W : ℕ) (H : ℝ) : 0 ≤ flatInverseRadius k W H := by
  unfold flatInverseRadius
  positivity

/-- The inverse theorem, primitive-center exclusion, and actual power
windows together remove every nonzero low-energy grid point once all
displayed finite parameter inequalities hold. -/
theorem unreserved_lowEnergyGrid_empty (N c k F W X : ℕ) (w : ℕ → ℕ)
    (hc : 0 < c) (hcN : c ≤ N) (hk : 20 ≤ k)
    (hw : AntitoneOn w (Set.Iio F)) (hmass : weightMass F w = k + 1)
    (H E s : ℝ) (hXV : X ≤ unreservedEndpoint N k + 1) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial F w) ^ 2 * H / 4 + 1) +
      (flatPolynomial F w).natDegree ≤ unreservedEndpoint N k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k u b X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E)
    (hρ : flatInverseRadius k W H ≤ 1)
    (hs : 1000 * (k : ℝ) ≤ s) (hρs : flatInverseRadius k W H * s ^ k ≤ 1)
    (hlog : 1 ≤ Real.log (s / (1000 * (k : ℝ))))
    (hA : (258 : ℝ) ≤ s) (hNk : 32 * (k : ℝ) ≤ N) (hNA : (4128 : ℝ) ≤ N)
    (hroot : Real.log ((N : ℝ) + 1) ≤ (k : ℝ) * Real.log (3 / 2))
    (hfloor : H < windowEnergyFloor N k s) :
    nonzeroFrequencies (c ^ k) ∩
      lowEnergyGrid (c ^ k) k (unreservedEndpoint N k + 1) H = ∅ := by
  apply nonzero_lowEnergyGrid_empty (unreservedPopulation N k) (c ^ k) k
    (unreservedEndpoint N k + 1) (pow_pos hc _) H (flatInverseRadius k W H)
    (unreservedPopulation_subset_prefix N k)
  · exact lowEnergyGrid_subset_integerArcs F w (c ^ k) k (unreservedEndpoint N k + 1)
      W X (pow_pos hc _) hw hmass H E hXV hW hlarge
      (by simpa only [Nat.cast_add, Nat.cast_one] using hsize) hcenter hbudget hρ
  · intro h hh
    exact hfloor.trans_le (unreserved_small_numerator_energy_lower N c k hc hcN hk s
      (flatInverseRadius k W H) hs (flatInverseRadius_nonneg k W H) hρs hlog hA hNk hNA hroot h hh)

theorem powerCollisionSum_le_of_empty_exceptional (R : Finset ℕ) (hR : R.Nonempty)
    (q k t V : ℕ) (H D : ℝ)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hempty : nonzeroFrequencies q ∩ lowEnergyGrid q k V H = ∅) :
    powerCollisionSum R k q t ≤ (q : ℝ) * Real.exp (-(t : ℝ) * (H - D) / R.card) := by
  have hc : (nonzeroFrequencies q ∩ lowEnergyGrid q k V H).card ≤ 0 := by simp only [hempty, Finset.card_empty, le_refl]
  have hs : ∀ h ∈ nonzeroFrequencies q, h ∈ lowEnergyGrid q k V H →
      (0 : ℝ) ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) :=
    fun h _ _ => finiteSineEnergy_nonneg R _
  have h := powerCollisionSum_le_exceptional_count R hR q k t V 0 D H 0 hmissing hc hs
  simpa only [Nat.cast_zero, zero_mul, add_zero] using h

theorem unreserved_collisionSum_le (N q k t : ℕ) (hk : 20 ≤ k)
    (hNk : 32 * (k : ℝ) ≤ N) (H : ℝ)
    (hempty : nonzeroFrequencies q ∩ lowEnergyGrid q k (unreservedEndpoint N k + 1) H = ∅) :
    powerCollisionSum (unreservedPopulation N k) k q t ≤
      (q : ℝ) * Real.exp (-(t : ℝ) * (H - 257) / (unreservedPopulation N k).card) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hU := unreservedEndpoint_ge_three_quarters N k (by omega)
  have hU1 : 1 ≤ unreservedEndpoint N k := by
    have h : (1 : ℝ) ≤ unreservedEndpoint N k := by linarith
    exact_mod_cast h
  apply powerCollisionSum_le_of_empty_exceptional (unreservedPopulation N k)
    (unreservedPopulation_nonempty N k hU1) q k t (unreservedEndpoint N k + 1) H 257
  · exact_mod_cast unreservedPopulation_missing_le N k (unreservedEndpoint N k + 1) le_rfl
  · exact hempty

end Erdos345
