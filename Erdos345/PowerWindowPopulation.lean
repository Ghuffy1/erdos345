import Erdos345.PowerWindowGeometry

namespace Erdos345

theorem powerWindowLower_ge_scale (r : ℝ) (hr : 0 ≤ r) (k j : ℕ) (hj : 1 ≤ j) :
    r ≤ powerWindowLower r k j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : 1 ≤ ((j : ℝ) + 1 / 8) ^ ((k : ℝ)⁻¹) :=
    Real.one_le_rpow (by linarith) (by positivity)
  simpa only [powerWindowLower, mul_one] using mul_le_mul_of_nonneg_left hp hr

theorem powerWindowUpper_le_bound (r : ℝ) (hr : 0 ≤ r) (k j Y : ℕ) (hjY : j ≤ Y) :
    powerWindowUpper r k j ≤ r * ((Y : ℝ) + 1) ^ ((k : ℝ)⁻¹) := by
  have hjYR : (j : ℝ) ≤ Y := by exact_mod_cast hjY
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)) hr

theorem powerWindow_subset_population (R : Finset ℕ) (A U k j Y : ℕ)
    (r : ℝ) (hr : 0 ≤ r) (hj : 1 ≤ j) (hjY : j ≤ Y)
    (hA : (A : ℝ) ≤ r) (hU : r * ((Y : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ U)
    (hpopulation : Finset.Icc A U ⊆ R) :
    naturalWindow (powerWindowLower r k j) (powerWindowUpper r k j) ⊆ R := by
  intro n hn
  have hb : 0 ≤ powerWindowUpper r k j := by unfold powerWindowUpper; positivity
  obtain ⟨hl, hu⟩ := (mem_naturalWindow _ _ hb n).mp hn
  have hnA : (A : ℝ) ≤ n := hA.trans ((powerWindowLower_ge_scale r hr k j hj).trans hl)
  have hnU : (n : ℝ) ≤ U := hu.trans ((powerWindowUpper_le_bound r hr k j Y hjY).trans hU)
  apply hpopulation
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hnA, by exact_mod_cast hnU⟩

theorem powerWindow_length_ge_two (r : ℝ) (hr : 0 ≤ r) (k j Y : ℕ)
    (hk : 0 < k) (hj : 1 ≤ j) (hjY : j ≤ Y)
    (hsize : 16 * (k : ℝ) * ((Y : ℝ) + 1) ≤ r) :
    2 ≤ powerWindowUpper r k j - powerWindowLower r k j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjYR : (j : ℝ) ≤ Y := by exact_mod_cast hjY
  have hd : 0 < 8 * (k : ℝ) * ((j : ℝ) + 1) := by positivity
  have hn : 2 * (8 * (k : ℝ) * ((j : ℝ) + 1)) ≤ r := by nlinarith
  exact ((le_div_iff₀ hd).mpr hn).trans (powerWindow_length_lower r hr k j hk hj)

/-- Finite stacked energy for the actual power phase on an available
integer band. Every interval length and membership condition is proved
from the displayed scale and endpoint inequalities. -/
theorem powerWindows_energy_lower (R : Finset ℕ) (A U k Y : ℕ) (hk : 0 < k)
    (r : ℝ) (hr : 0 < r)
    (hsize : 16 * (k : ℝ) * ((Y : ℝ) + 1) ≤ r)
    (hA : (A : ℝ) ≤ r) (hU : r * ((Y : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ U)
    (hpopulation : Finset.Icc A U ⊆ R) :
    r / (256 * (k : ℝ)) * (∑ j ∈ Finset.Icc 1 Y, 1 / ((j : ℝ) + 1)) ≤
      finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  let J := Finset.Icc 1 Y
  let a := powerWindowLower r k
  let b := powerWindowUpper r k
  let z := fun j : ℕ => (j : ℤ)
  have hz : Set.InjOn z (J : Set ℕ) := by
    intro i _ j _ hij
    change (i : ℤ) = (j : ℤ) at hij
    exact_mod_cast hij
  have hphase : ∀ j ∈ J, ∀ n ∈ naturalWindow (a j) (b j),
      (z j : ℝ) + 1 / 8 ≤ ((n : ℝ) / r) ^ k ∧
      ((n : ℝ) / r) ^ k ≤ (z j : ℝ) + 1 / 4 := by
    intro j _ n hn
    simpa only [z, Int.cast_natCast] using powerWindow_phase r hr k j n hk hn
  have henergy := stacked_naturalWindow_energy_lower R J (fun n => ((n : ℝ) / r) ^ k)
    a b z hz (fun j _ => powerWindowLower_nonneg r hr.le k j)
    (fun j hj => powerWindow_length_ge_two r hr.le k j Y hk
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hsize)
    (fun j hj => powerWindow_subset_population R A U k j Y r hr.le
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hA hU hpopulation) hphase
  have hsum : r / (8 * (k : ℝ)) * (∑ j ∈ J, 1 / ((j : ℝ) + 1)) ≤
      ∑ j ∈ J, (b j - a j) := by
    calc
      _ = ∑ j ∈ J, r / (8 * (k : ℝ) * ((j : ℝ) + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_mul_div_comm, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => powerWindow_length_lower r hr.le k j hk
        (Finset.mem_Icc.mp hj).1)
  have hdiv := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 32)
  have hfinal := hdiv.trans henergy
  convert hfinal using 1
  dsimp only [J]
  ring

end Erdos345
