import Erdos345.PowerWindowPopulation
import Erdos345.SmallNumeratorGrid

namespace Erdos345

noncomputable def positivePhaseScale (q h k : ℕ) : ℝ :=
  ((q : ℝ) / h) ^ ((k : ℝ)⁻¹)

theorem positivePhaseScale_pos (q h k : ℕ) (hq : 0 < q) (hh : 0 < h) :
    0 < positivePhaseScale q h k := by
  unfold positivePhaseScale
  apply Real.rpow_pos_of_pos
  positivity

theorem positivePhaseScale_pow (q h k : ℕ) (hq : 0 < q) (hh : 0 < h) (hk : 0 < k) :
    positivePhaseScale q h k ^ k = (q : ℝ) / h := by
  unfold positivePhaseScale
  exact Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hk)

theorem power_phase_eq_scaled (q h k n : ℕ) (hq : 0 < q) (hh : 0 < h) (hk : 0 < k) :
    (h : ℝ) / q * (n : ℝ) ^ k = ((n : ℝ) / positivePhaseScale q h k) ^ k := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  rw [div_pow, positivePhaseScale_pow q h k hq hh hk]
  field_simp

theorem finiteSineEnergy_eq_scaled (R : Finset ℕ) (q h k : ℕ)
    (hq : 0 < q) (hh : 0 < h) (hk : 0 < k) :
    finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) =
      finiteSineEnergy R (fun n => ((n : ℝ) / positivePhaseScale q h k) ^ k) := by
  unfold finiteSineEnergy
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [power_phase_eq_scaled q h k n hq hh hk]

theorem sine_square_complement_numerator (q h k n : ℕ) (hq : 0 < q) (hh : h ≤ q) :
    Real.sin (Real.pi * ((q - h : ℕ) : ℝ) / q * (n : ℝ) ^ k) ^ 2 =
      Real.sin (Real.pi * (h : ℝ) / q * (n : ℝ) ^ k) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  let x := (h : ℝ) / q * (n : ℝ) ^ k
  let z : ℤ := (n ^ k : ℕ)
  have harg : Real.pi * ((q - h : ℕ) : ℝ) / q * (n : ℝ) ^ k =
      -(Real.pi * (x - (z : ℝ))) := by
    dsimp only [x, z]
    rw [Nat.cast_sub hh, Int.cast_natCast, Nat.cast_pow]
    field_simp
    ring
  rw [harg, Real.sin_neg, neg_sq, sin_square_sub_integer]
  dsimp only [x]
  congr 2
  ring

theorem finiteSineEnergy_complement_numerator (R : Finset ℕ) (q h k : ℕ)
    (hq : 0 < q) (hh : h ≤ q) :
    finiteSineEnergy R (fun n => ((q - h : ℕ) : ℝ) / q * (n : ℝ) ^ k) =
      finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) := by
  unfold finiteSineEnergy
  apply Finset.sum_congr rfl
  intro n _
  simpa only [mul_div_assoc, mul_assoc] using sine_square_complement_numerator q h k n hq hh

theorem finiteSineEnergy_min_numerator (R : Finset ℕ) (q h k : ℕ)
    (hq : 0 < q) (hh : h ≤ q) :
    finiteSineEnergy R (fun n => ((min h (q - h) : ℕ) : ℝ) / q * (n : ℝ) ^ k) =
      finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) := by
  by_cases he : h ≤ q - h
  · simp only [min_eq_left he]
  · rw [min_eq_right (le_of_not_ge he)]
    exact finiteSineEnergy_complement_numerator R q h k hq hh

end Erdos345
