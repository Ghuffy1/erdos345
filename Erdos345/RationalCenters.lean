import Erdos345.SineEnergyPerturbation
import Mathlib.Data.Rat.Lemmas

namespace Erdos345

open Finset

theorem power_sineEnergy_abs (α : ℝ) (k X : ℕ) :
    sineEnergy (fun n => α * (n : ℝ) ^ k) X =
      sineEnergy (fun n => |α| * (n : ℝ) ^ k) X := by
  by_cases hα : 0 ≤ α
  · rw [abs_of_nonneg hα]
  · rw [abs_of_neg (lt_of_not_ge hα)]
    unfold sineEnergy
    apply sum_congr rfl
    intro n _
    rw [show Real.pi * ((-α) * (n : ℝ) ^ k) = -(Real.pi * (α * (n : ℝ) ^ k)) by ring,
      Real.sin_neg, neg_sq]

theorem rational_sineEnergy_eq_center (β : ℚ) (k X : ℕ) :
    sineEnergy (fun n => (β : ℝ) * (n : ℝ) ^ k) X =
      centerEnergy k β.num.natAbs β.den X := by
  have hden : (0 : ℝ) < β.den := by exact_mod_cast β.den_pos
  have habs : |(β : ℝ)| = (β.num.natAbs : ℝ) / (β.den : ℝ) := by
    rw [Rat.cast_def, abs_div, abs_of_pos hden, Nat.cast_natAbs, Int.cast_abs]
  rw [power_sineEnergy_abs, habs]
  unfold sineEnergy centerEnergy centerTerm
  apply sum_congr rfl
  intro n _
  congr 2
  ring

theorem rational_fraction_den_dvd (u : ℤ) (B : ℕ) : ((u : ℚ) / B).den ∣ B := by
  have h := Rat.den_dvd u (B : ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact_mod_cast h

theorem rational_fraction_den_gt_one (u : ℤ) (B : ℕ) (hB : 0 < B)
    (hnot : ¬(B : ℤ) ∣ u) : 1 < ((u : ℚ) / B).den := by
  have hden : ((u : ℚ) / B).den ≠ 1 := by
    intro h
    have heq := Rat.den_div_intCast_eq_one_iff u (B : ℤ) (by exact_mod_cast Nat.ne_of_gt hB)
    rw [Int.cast_natCast] at heq
    exact hnot (heq.mp h)
  have hpos := ((u : ℚ) / B).den_pos
  omega

/-- Primitive center bounds apply to every noninteger rational with a
denominator dividing the same modulus, including negative numerators. -/
theorem rational_center_energy_gt (k X B : ℕ) (hB : 0 < B) (E : ℝ)
    (hcenter : ∀ q v : ℕ, 1 < q → v.Coprime q → q ∣ B → E < centerEnergy k v q X)
    (u : ℤ) (hnot : ¬(B : ℤ) ∣ u) :
    E < sineEnergy (fun n => ((u : ℝ) / B) * (n : ℝ) ^ k) X := by
  let β : ℚ := (u : ℚ) / B
  have hq : 1 < β.den := rational_fraction_den_gt_one u B hB hnot
  have hd : β.den ∣ B := rational_fraction_den_dvd u B
  have h := hcenter β.den β.num.natAbs hq β.reduced hd
  rw [← rational_sineEnergy_eq_center β k X] at h
  simpa only [β, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h

end Erdos345
