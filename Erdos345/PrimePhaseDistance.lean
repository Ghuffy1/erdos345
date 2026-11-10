import Erdos345.BelovProfileBudget
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Associated

namespace Erdos345

noncomputable def primePhaseDistance (y : ℝ) (p : ℕ) : ℝ :=
  |y - (p : ℝ) * (round (y / p) : ℤ)|

noncomputable def primePhaseBin (y : ℝ) (p : ℕ) : ℕ := ⌊primePhaseDistance y p⌋₊

theorem primePhaseDistance_nonneg (y : ℝ) (p : ℕ) : 0 ≤ primePhaseDistance y p := abs_nonneg _

theorem primePhaseDistance_eq (y : ℝ) (p : ℕ) (hp : 0 < p) :
    primePhaseDistance y p = (p : ℝ) * |y / p - (round (y / p) : ℤ)| := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    primePhaseDistance y p = |(p : ℝ) * (y / p - (round (y / p) : ℤ))| := by
      unfold primePhaseDistance
      congr 1
      field_simp
    _ = _ := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]

theorem primePhaseDistance_le_half (y : ℝ) (p : ℕ) (hp : 0 < p) :
    primePhaseDistance y p ≤ (p : ℝ) / 2 := by
  rw [primePhaseDistance_eq y p hp]
  have h := mul_le_mul_of_nonneg_left (abs_sub_round (y / p)) (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  nlinarith

theorem primePhaseBin_le_distance (y : ℝ) (p : ℕ) :
    (primePhaseBin y p : ℝ) ≤ primePhaseDistance y p := Nat.floor_le (primePhaseDistance_nonneg y p)

theorem primePhaseBin_dvd_alternative (y : ℝ) (p : ℕ) :
    (p : ℤ) ∣ ⌊y⌋ - (primePhaseBin y p : ℤ) ∨
      (p : ℤ) ∣ ⌊-y⌋ - (primePhaseBin y p : ℤ) := by
  let k : ℤ := round (y / p)
  have hbin : (primePhaseBin y p : ℤ) = ⌊|y - (p : ℝ) * (k : ℝ)|⌋ :=
    Int.natCast_floor_eq_floor (primePhaseDistance_nonneg y p)
  by_cases hsign : 0 ≤ y - (p : ℝ) * (k : ℝ)
  · left
    rw [abs_of_nonneg hsign] at hbin
    have heq : y - (p : ℝ) * (k : ℝ) = y - ((p : ℤ) * k : ℤ) := by push_cast; rfl
    rw [heq, Int.floor_sub_intCast] at hbin
    exact ⟨k, by omega⟩
  · right
    rw [abs_of_nonpos (le_of_not_ge hsign)] at hbin
    have heq : -(y - (p : ℝ) * (k : ℝ)) = -y + ((p : ℤ) * k : ℤ) := by push_cast; ring
    rw [heq, Int.floor_add_intCast] at hbin
    refine ⟨-k, ?_⟩
    calc
      ⌊-y⌋ - (primePhaseBin y p : ℤ) = -((p : ℤ) * k) := by omega
      _ = _ := by ring

end Erdos345
