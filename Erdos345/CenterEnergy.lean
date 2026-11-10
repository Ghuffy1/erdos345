import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
The elementary last step in the rational-center argument. These are statements
about the original phase, with the original denominator. No CRT projection or
analytic small-denominator reduction is assumed here.
-/

namespace Erdos345

open Finset

theorem sin_pi_mul_half_lower {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (Real.pi * x) := by
  have h := Real.le_sin_mul (x := 2 * x) (by linarith) (by linarith)
  have heq : Real.pi / 2 * (2 * x) = Real.pi * x := by ring
  rwa [heq] at h

theorem sin_pi_mul_lower {q x : ℝ} (hq : 0 < q)
    (hlo : 1 / q ≤ x) (hhi : x ≤ 1 - 1 / q) :
    2 / q ≤ Real.sin (Real.pi * x) := by
  have hqinv : 0 < 1 / q := one_div_pos.mpr hq
  simp only [div_eq_mul_inv] at *
  by_cases hh : x ≤ 1 / 2
  · have h := sin_pi_mul_half_lower (by linarith) hh
    linarith
  · have h := sin_pi_mul_half_lower (x := 1 - x) (by linarith) (by linarith)
    have heq : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [heq, Real.sin_pi_sub] at h
    linarith

theorem sin_nat_fraction_sq_lower {u q : ℕ} (hu : 0 < u) (huq : u < q) :
    4 / (q : ℝ) ^ 2 ≤ Real.sin (Real.pi * (u : ℝ) / (q : ℝ)) ^ 2 := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast hu.trans huq
  have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hu1q : (u : ℝ) + 1 ≤ q := by exact_mod_cast huq
  have hlo : 1 / (q : ℝ) ≤ (u : ℝ) / q := (div_le_div_iff_of_pos_right hq).mpr hu1
  have hhi : (u : ℝ) / q ≤ 1 - 1 / q := by
    apply (div_le_iff₀ hq).mpr
    simp only [sub_mul, one_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq)]
    linarith
  have h := sin_pi_mul_lower hq hlo hhi
  have harg : Real.pi * ((u : ℝ) / q) = Real.pi * u / q := by ring
  rw [harg] at h
  have hsq : (2 / (q : ℝ)) ^ 2 ≤ Real.sin (Real.pi * u / q) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  convert hsq using 1
  ring

theorem sin_nat_fraction_sq_mod (a q : ℕ) (hq : 0 < q) :
    Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) ^ 2 =
      Real.sin (Real.pi * ((a % q : ℕ) : ℝ) / (q : ℝ)) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hsplit : (a : ℝ) = (a % q : ℕ) + (q : ℝ) * (a / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div a q).symm
  have harg : Real.pi * (a : ℝ) / (q : ℝ) =
      Real.pi * ((a % q : ℕ) : ℝ) / (q : ℝ) + ((a / q : ℕ) : ℝ) * Real.pi := by
    rw [hsplit]
    field_simp
  rw [harg, Real.sin_add_nat_mul_pi, mul_pow]
  have hsign : ((-1 : ℝ) ^ (a / q)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (a / q) 2, pow_mul]
    norm_num
  rw [hsign, one_mul]

noncomputable def centerTerm (k u q n : ℕ) : ℝ :=
  Real.sin (Real.pi * (u : ℝ) * (n : ℝ) ^ k / (q : ℝ)) ^ 2

noncomputable def centerEnergy (k u q X : ℕ) : ℝ := ∑ n ∈ range X, centerTerm k u q n

theorem centerTerm_nonneg (k u q n : ℕ) : 0 ≤ centerTerm k u q n := sq_nonneg _

theorem centerTerm_residue_one (k u q j : ℕ) (hu : 0 < u) (huq : u < q) :
    4 / (q : ℝ) ^ 2 ≤ centerTerm k u q (q * j + 1) := by
  have hq : 0 < q := hu.trans huq
  have hbase : Nat.ModEq q (q * j + 1) 1 := Nat.ModEq.modulus_mul_add
  have hp : Nat.ModEq q (u * (q * j + 1) ^ k) u := by
    simpa only [one_pow, mul_one] using (Nat.ModEq.refl u).mul (hbase.pow k)
  have hmod : (u * (q * j + 1) ^ k) % q = u := by
    calc
      _ = u % q := hp
      _ = u := Nat.mod_eq_of_lt huq
  have hphase : centerTerm k u q (q * j + 1) =
      Real.sin (Real.pi * ((u * (q * j + 1) ^ k : ℕ) : ℝ) / (q : ℝ)) ^ 2 := by
    simp only [centerTerm, Nat.cast_mul, Nat.cast_pow, mul_assoc]
  rw [hphase, sin_nat_fraction_sq_mod _ _ hq, hmod]
  exact sin_nat_fraction_sq_lower hu huq

/-- Every full block of q inputs has a residue-one contribution. -/
theorem centerEnergy_lower (k u q X : ℕ) (hu : 0 < u) (huq : u < q) :
    4 * ((X / q : ℕ) : ℝ) / (q : ℝ) ^ 2 ≤ centerEnergy k u q X := by
  classical
  have hq : 0 < q := hu.trans huq
  have hq2 : 2 ≤ q := by omega
  let S := (range (X / q)).image fun j => q * j + 1
  have hsub : S ⊆ range X := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    have hj' : j + 1 ≤ X / q := mem_range.mp hj
    have hm := Nat.mul_le_mul_left q hj'
    have hdiv := Nat.div_mul_le_self X q
    rw [Nat.mul_comm (X / q) q] at hdiv
    apply mem_range.mpr
    nlinarith
  have hinj : Function.Injective (fun j : ℕ => q * j + 1) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel h)
  have hcard : S.card = X / q := by
    rw [show S = (range (X / q)).image (fun j => q * j + 1) from rfl,
      card_image_of_injective _ hinj, card_range]
  calc
    4 * ((X / q : ℕ) : ℝ) / (q : ℝ) ^ 2 = ∑ _ ∈ S, 4 / (q : ℝ) ^ 2 := by
      simp only [sum_const, hcard, nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ S, centerTerm k u q n := by
      apply sum_le_sum
      intro n hn
      obtain ⟨j, _, rfl⟩ := mem_image.mp hn
      exact centerTerm_residue_one k u q j hu huq
    _ ≤ centerEnergy k u q X := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro n _ _
      exact centerTerm_nonneg k u q n

/-- A completely explicit sufficient condition for the final contradiction. -/
theorem centerEnergy_gt_of_cubic_bound (k u q X : ℕ)
    (hu : 0 < u) (huq : u < q) (hX : q ^ 3 * (k ^ 2 + 1) ≤ X) :
    (k : ℝ) ^ 2 < centerEnergy k u q X := by
  have hq : 0 < q := hu.trans huq
  have hcount : q ^ 2 * (k ^ 2 + 1) ≤ X / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      q ^ 2 * (k ^ 2 + 1) * q = q ^ 3 * (k ^ 2 + 1) := by ring
      _ ≤ X := hX
  have hcountR : (q : ℝ) ^ 2 * ((k : ℝ) ^ 2 + 1) ≤ ((X / q : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq2 : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqR
  have hstrict : (k : ℝ) ^ 2 * (q : ℝ) ^ 2 < 4 * ((X / q : ℕ) : ℝ) := by
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hq2.le]
  exact ((lt_div_iff₀ hq2).mpr hstrict).trans_le (centerEnergy_lower k u q X hu huq)

theorem low_centerEnergy_forces_cubic_bound (k u q X : ℕ)
    (hu : 0 < u) (huq : u < q) (hE : centerEnergy k u q X ≤ (k : ℝ) ^ 2) :
    X < q ^ 3 * (k ^ 2 + 1) := by
  by_contra h
  exact (not_lt_of_ge hE)
    (centerEnergy_gt_of_cubic_bound k u q X hu huq (Nat.le_of_not_gt h))

end Erdos345
