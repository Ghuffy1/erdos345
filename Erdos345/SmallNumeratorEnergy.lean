import Erdos345.FirstPowerWindow
import Erdos345.MiddlePowerWindows
import Erdos345.PowerScaleBounds

namespace Erdos345

noncomputable def windowEnergyFloor (N k : ℕ) (s : ℝ) : ℝ :=
  min ((N : ℝ) / (512 * (k : ℝ)))
    (s / (256 * (k : ℝ)) * (Real.log (s / (1000 * (k : ℝ))) - 1))

theorem uniform_scaled_energy_lower (R : Finset ℕ) (A U N k : ℕ) (hk : 0 < k)
    (s r : ℝ) (hs : 1000 * (k : ℝ) ≤ s) (hsr : s ≤ r) (hrN : r ≤ N)
    (hlog : 1 ≤ Real.log (s / (1000 * (k : ℝ))))
    (hA : (A : ℝ) ≤ s) (hNk : 32 * (k : ℝ) ≤ N) (hNA : 16 * (A : ℝ) ≤ N)
    (hroot : ((N : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ 3 / 2)
    (hfirst : (N : ℝ) * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ U)
    (hmiddle : 3 * (N : ℝ) / 4 ≤ U) (hpopulation : Finset.Icc A U ⊆ R) :
    windowEnergyFloor N k s ≤ finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := hs0.trans_le hsr
  by_cases hrhalf : r ≤ (N : ℝ) / 2
  · have he := middle_scale_energy_lower R A U N k hk r (hs.trans hsr) hrhalf
      hroot hmiddle (hA.trans hsr) hpopulation
    have hratio : s / (1000 * (k : ℝ)) ≤ r / (1000 * (k : ℝ)) := by gcongr
    have hl : Real.log (s / (1000 * (k : ℝ))) ≤ Real.log (r / (1000 * (k : ℝ))) :=
      Real.log_le_log (by positivity) hratio
    have hp : s / (256 * (k : ℝ)) * (Real.log (s / (1000 * (k : ℝ))) - 1) ≤
        r / (256 * (k : ℝ)) * (Real.log (r / (1000 * (k : ℝ))) - 1) := by
      exact mul_le_mul (by gcongr) (sub_le_sub_right hl 1) (sub_nonneg.mpr hlog) (by positivity)
    exact (min_le_right _ _).trans (hp.trans he)
  · have he := large_scale_energy_lower R A U N k hk r (le_of_not_ge hrhalf)
      hrN hNk hNA hfirst hpopulation
    exact (min_le_left _ _).trans he

/-- The actual modular power phase has a uniform energy lower bound
for every nonzero frequency in the small end-numerator range. This
discharges the corresponding energy premise of the collision theorem
under explicit finite scale and population conditions. -/
theorem small_numerator_energy_lower (R : Finset ℕ) (A U N c k : ℕ)
    (hc : 0 < c) (hcN : c ≤ N) (hk : 0 < k) (s ρ : ℝ)
    (hs : 1000 * (k : ℝ) ≤ s) (hρ : 0 ≤ ρ) (hρs : ρ * s ^ k ≤ 1)
    (hlog : 1 ≤ Real.log (s / (1000 * (k : ℝ))))
    (hA : (A : ℝ) ≤ s) (hNk : 32 * (k : ℝ) ≤ N) (hNA : 16 * (A : ℝ) ≤ N)
    (hroot : ((N : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ 3 / 2)
    (hfirst : (N : ℝ) * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ U)
    (hmiddle : 3 * (N : ℝ) / 4 ≤ U) (hpopulation : Finset.Icc A U ⊆ R)
    (h : ℕ) (hh : h ∈ smallNumeratorFrequencies (c ^ k) ⌊((c ^ k : ℕ) : ℝ) * ρ⌋₊) :
    windowEnergyFloor N k s ≤
      finiteSineEnergy R (fun n => (h : ℝ) / (c ^ k : ℕ) * (n : ℝ) ^ k) := by
  let q := c ^ k
  let m := min h (q - h)
  obtain ⟨hh0, hhq, hmBound⟩ := (mem_smallNumeratorFrequencies q _ h).mp hh
  have hq : 0 < q := pow_pos hc _
  have hm : 0 < m := lt_min (Nat.pos_of_ne_zero hh0) (Nat.sub_pos_of_lt hhq)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : 0 < s := by linarith
  have hmρ : (m : ℝ) ≤ (q : ℝ) * ρ :=
    (by exact_mod_cast hmBound : (m : ℝ) ≤ (⌊(q : ℝ) * ρ⌋₊ : ℝ)).trans
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hρ))
  have hmPower : (m : ℝ) * s ^ k ≤ q := by
    calc
      _ ≤ ((q : ℝ) * ρ) * s ^ k := mul_le_mul_of_nonneg_right hmρ (pow_nonneg hs0.le _)
      _ = (q : ℝ) * (ρ * s ^ k) := by ring
      _ ≤ (q : ℝ) * 1 := mul_le_mul_of_nonneg_left hρs (Nat.cast_nonneg _)
      _ = _ := mul_one _
  have hsr := positivePhaseScale_ge q m k hq hm hk s hs0.le hmPower
  have hrN : positivePhaseScale q m k ≤ N :=
    (positivePhaseScale_le_base c m k hc hm hk).trans (by exact_mod_cast hcN)
  have he := uniform_scaled_energy_lower R A U N k hk s (positivePhaseScale q m k)
    hs hsr hrN hlog hA hNk hNA hroot hfirst hmiddle hpopulation
  rw [← finiteSineEnergy_eq_scaled R q m k hq hm hk] at he
  exact he.trans_eq (finiteSineEnergy_min_numerator R q h k hq hhq.le)

end Erdos345
