import Erdos345.RadialLogSeries

namespace Erdos345

open Finset

def flatCosineNonnegative (N : ℕ) (w : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ a + ∑ i ∈ range N, (w i : ℝ) * (z ^ (i + 1)).re

theorem radialFlatProduct_ne_zero (N : ℕ) (w : ℕ → ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : radialFlatProduct N w r z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (unit_radial_factor_ne_zero (z ^ (i + 1))
    (by simp only [norm_pow, hz, one_pow]) r hr hr1)

theorem radial_log_upper_of_cosine (N : ℕ) (w : ℕ → ℕ) (a : ℝ)
    (hcos : flatCosineNonnegative N w a) (z : ℂ) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log ‖radialFlatProduct N w r z‖ ≤ a * Real.log (1 / (1 - r)) := by
  have hnorm : ‖1 - (r : ℂ) * 1‖ = 1 - r := by
    have heq : (1 - (r : ℂ) * 1) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1)]
  have hb : HasSum (fun m : ℕ => r ^ m / (m : ℝ)) (-Real.log (1 - r)) := by
    have h := unit_radial_log_hasSum (1 : ℂ) (by norm_num) r hr hr1
    rw [hnorm] at h
    simpa only [one_pow, Complex.one_re, mul_one] using h
  have hsum := radialFlatProduct_log_hasSum N w z hz r hr hr1
  have hleft := hb.mul_left (-a)
  have hpoint : ∀ m : ℕ, (-a) * (r ^ m / (m : ℝ)) ≤
      (r ^ m / (m : ℝ)) * ∑ i ∈ range N, (w i : ℝ) * (z ^ ((i + 1) * m)).re := by
    intro m
    have h := hcos (z ^ m) (by simp only [norm_pow, hz, one_pow])
    have heq : (∑ i ∈ range N, (w i : ℝ) * ((z ^ m) ^ (i + 1)).re) =
        ∑ i ∈ range N, (w i : ℝ) * (z ^ ((i + 1) * m)).re := by
      apply sum_congr rfl
      intro i _
      rw [← pow_mul, Nat.mul_comm m (i + 1)]
    rw [heq] at h
    have hnonneg : 0 ≤ r ^ m / (m : ℝ) := div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left (show -a ≤ ∑ i ∈ range N, (w i : ℝ) * (z ^ ((i + 1) * m)).re by linarith) hnonneg
    nlinarith
  have hbound := hasSum_le hpoint hleft hsum
  rw [Real.log_div one_ne_zero (ne_of_gt (sub_pos.mpr hr1)), Real.log_one, zero_sub]
  nlinarith

theorem flatPolynomial_sup_norm_from_cosine (N : ℕ) (w : ℕ → ℕ) (a : ℝ)
    (hcos : flatCosineNonnegative N w a) (z : ℂ) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖((flatPolynomial N w).map (Int.castRingHom ℂ)).eval z‖ ≤
      Real.exp ((weightMass N w : ℝ) * Real.log (2 / (1 + r)) + a * Real.log (1 / (1 - r))) := by
  have hrad : ‖radialFlatProduct N w r z‖ ≤ Real.exp (a * Real.log (1 / (1 - r))) :=
    (Real.log_le_iff_le_exp (norm_pos_iff.mpr (radialFlatProduct_ne_zero N w z hz r hr hr1))).mp
      (radial_log_upper_of_cosine N w a hcos z hz r hr hr1)
  have h := (flatPolynomial_norm_le_radial N w z hz r hr).trans
    (mul_le_mul_of_nonneg_left hrad (by positivity : 0 ≤ (2 / (1 + r)) ^ weightMass N w))
  have hpow : (2 / (1 + r)) ^ weightMass N w =
      Real.exp ((weightMass N w : ℝ) * Real.log (2 / (1 + r))) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 2 / (1 + r))]
  rw [hpow, ← Real.exp_add] at h
  exact h

theorem flatPolynomial_sup_norm_mass_bound (N : ℕ) (w : ℕ → ℕ) (a : ℝ)
    (hcos : flatCosineNonnegative N w a) (hJ : 0 < weightMass N w)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖((flatPolynomial N w).map (Int.castRingHom ℂ)).eval z‖ ≤
      Real.exp (1 + a * Real.log (weightMass N w : ℝ)) := by
  let J : ℝ := weightMass N w
  let r := 1 - 1 / J
  have hJ1 : 1 ≤ J := by dsimp only [J]; exact_mod_cast (show 1 ≤ weightMass N w from hJ)
  have hJpos : 0 < J := by linarith
  have hr : 0 ≤ r := by
    dsimp only [r]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hJ1
    norm_num only [one_div_one] at h
    exact sub_nonneg.mpr h
  have hr1 : r < 1 := by dsimp only [r]; have h := one_div_pos.mpr hJpos; linarith
  have hp : 0 < 1 + r := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hp)
  have hratio : J * (2 / (1 + r) - 1) ≤ 1 := by
    have hJr : J * r = J - 1 := by dsimp only [r]; field_simp [ne_of_gt hJpos]
    calc
      _ = (2 * J - J * (1 + r)) / (1 + r) := by field_simp [ne_of_gt hp]
      _ ≤ 1 := (div_le_iff₀ hp).mpr (by nlinarith)
  have hscale : J * Real.log (2 / (1 + r)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlog hJpos.le).trans hratio
  have hinv : 1 / (1 - r) = J := by dsimp only [r]; field_simp [ne_of_gt hJpos]; ring
  have h := flatPolynomial_sup_norm_from_cosine N w a hcos z hz r hr hr1
  rw [hinv] at h
  exact h.trans (Real.exp_le_exp.mpr (by change J * Real.log (2 / (1 + r)) + _ ≤ _; linarith))

end Erdos345
