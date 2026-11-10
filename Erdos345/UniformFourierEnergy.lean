import Erdos345.FourierDecay

namespace Erdos345

open Filter

theorem population_energy_gt_of_empty (R : Finset ℕ) (q k V : ℕ) (H D : ℝ)
    (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hempty : nonzeroFrequencies q ∩ lowEnergyGrid q k V H = ∅)
    (h : ℕ) (hh : h ∈ nonzeroFrequencies q) :
    H - D < finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) := by
  have hhq := ((mem_nonzeroFrequencies q h).mp hh).2
  have hprefix : H < sineEnergy (fun n => (h : ℝ) / q * (n : ℝ) ^ k) V := by
    by_contra hnot
    have hm : h ∈ nonzeroFrequencies q ∩ lowEnergyGrid q k V H :=
      Finset.mem_inter.mpr ⟨hh, (mem_lowEnergyGrid q k V h H).mpr ⟨hhq, le_of_not_gt hnot⟩⟩
    rw [hempty] at hm
    exact Finset.notMem_empty h hm
  have hp := prefixEnergy_le_population_add_missing R
    (fun n => (h : ℝ) / q * (n : ℝ) ^ k) V
  linarith

theorem uniform_energy_of_parameters (C : ℝ) (k : ℕ) (w : ℕ → ℕ)
    (hp : FourierParameterConditions C k w)
    (hw : AntitoneOn w (Set.Iio (k + 1))) (hmass : weightMass (k + 1) w = k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      (k : ℝ) ^ 2 < centerEnergy k u b (quasipolynomialCenterPrefix k C))
    (c : ℕ) (hc : 0 < c) (hcN : c ≤ fourierN k) (h : ℕ)
    (hh : h ∈ nonzeroFrequencies (c ^ k)) :
    fourierH k - 257 < finiteSineEnergy (unreservedPopulation (fourierN k) k)
      (fun n => (h : ℝ) / (c ^ k : ℕ) * (n : ℝ) ^ k) := by
  have hempty := (coarse_unreserved_frequency_bound (fourierN k) c k (k + 1)
    (fourierW k) (quasipolynomialCenterPrefix k C) w hc hcN hp.degree_large hw hmass
    (fourierH k) ((k : ℝ) ^ 2) (fourierH_nonneg k) (fourierW_le_N k) hp.coarse_window
    hp.center_inside hp.sampling_length hp.inverse_size hcenter hp.perturbation hp.root_budget).1
  apply population_energy_gt_of_empty (unreservedPopulation (fourierN k) k) (c ^ k) k
    (unreservedEndpoint (fourierN k) k + 1) (fourierH k) 257 _ hempty h hh
  exact_mod_cast unreservedPopulation_missing_le (fourierN k) k
    (unreservedEndpoint (fourierN k) k + 1) le_rfl

theorem good_degrees_uniform_energy
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ c : ℕ, 0 < c → c ≤ fourierN k → ∀ h ∈ nonzeroFrequencies (c ^ k),
        fourierH k - 257 < finiteSineEnergy (unreservedPopulation (fourierN k) k)
          (fun n => (h : ℝ) / (c ^ k : ℕ) * (n : ℝ) ^ k) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_fourier_parameter_conditions flatNormConstant flatNormConstant_nonneg)
  refine ⟨max 1 K, ?_⟩
  intro Y hY
  have hYpos : 0 < Y := by omega
  obtain ⟨k, hkY, hk2Y, hcenter⟩ := exists_good_center_bound_from_cosine_existence hinput Y hYpos
  have hkpos : 0 < k := hYpos.trans_le hkY
  obtain ⟨w, hw, hmass, hnorm⟩ := flat_family_from_cosine_existence hinput k hkpos k hkpos le_rfl
  have hparams := hK k (by omega) w hmass hnorm
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro c hc hcN h hh
  exact uniform_energy_of_parameters flatNormConstant k w hparams hw hmass hcenter c hc hcN h hh

end Erdos345
