import Erdos345.UnreservedPopulation
import Erdos345.SmallNumeratorEnergy

namespace Erdos345

theorem rpow_inv_le_of_log_budget (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (k : ℕ) (hk : 0 < k) (hlog : Real.log x ≤ (k : ℝ) * Real.log y) :
    x ^ ((k : ℝ)⁻¹) ≤ y := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos hx, ← Real.exp_log hy]
  apply Real.exp_le_exp.mpr
  have h : Real.log x / (k : ℝ) ≤ Real.log y :=
    (div_le_iff₀ hkR).mpr (by nlinarith only [hlog])
  simpa only [div_eq_mul_inv] using h

/-- The small-numerator energy bound specialized to the actual
unreserved positive population after removing bases 2 through 257.
All geometric window conditions follow from the displayed numerical
budgets; no separate energy hypothesis remains. -/
theorem unreserved_small_numerator_energy_lower (N c k : ℕ)
    (hc : 0 < c) (hcN : c ≤ N) (hk : 20 ≤ k) (s ρ : ℝ)
    (hs : 1000 * (k : ℝ) ≤ s) (hρ : 0 ≤ ρ) (hρs : ρ * s ^ k ≤ 1)
    (hlog : 1 ≤ Real.log (s / (1000 * (k : ℝ))))
    (hA : (258 : ℝ) ≤ s) (hNk : 32 * (k : ℝ) ≤ N) (hNA : (4128 : ℝ) ≤ N)
    (hroot : Real.log ((N : ℝ) + 1) ≤ (k : ℝ) * Real.log (3 / 2))
    (h : ℕ) (hh : h ∈ smallNumeratorFrequencies (c ^ k) ⌊((c ^ k : ℕ) : ℝ) * ρ⌋₊) :
    windowEnergyFloor N k s ≤
      finiteSineEnergy (unreservedPopulation N k)
        (fun n => (h : ℝ) / (c ^ k : ℕ) * (n : ℝ) ^ k) := by
  have hk0 : 0 < k := by omega
  apply small_numerator_energy_lower (unreservedPopulation N k) 258 (unreservedEndpoint N k)
    N c k hc hcN hk0 s ρ hs hρ hρs hlog hA hNk
  · norm_num
    exact_mod_cast hNA
  · exact rpow_inv_le_of_log_budget ((N : ℝ) + 1) (3 / 2) (by positivity) (by norm_num) k hk0 hroot
  · exact quarter_root_endpoint_le N k hk
  · exact unreservedEndpoint_ge_three_quarters N k (by omega)
  · exact unreservedPopulation_contains_band N k
  · exact hh

end Erdos345
