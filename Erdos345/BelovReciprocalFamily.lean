import Erdos345.BelovDyadicFamily
import Erdos345.DyadicSineFlattening

namespace Erdos345

abbrev BelovFamilyIndex (q : ℕ) :=
  Unit ⊕ DyadicSineIndex (belovLevelPrimes q) belovMultiplicity

noncomputable def belovFrequency (q : ℕ) : BelovFamilyIndex q → ℝ
  | .inl _ => 1
  | .inr a => dyadicFrequency (belovLevelPrimes q) belovMultiplicity a

noncomputable def belovDenominator (q : ℕ) (a : BelovFamilyIndex q) : ℝ :=
  (belovFrequency q a)⁻¹

theorem dyadicAtomFrequency_lt_multiplicity (j p v i : ℕ) (hp : 0 < p) (hi : i < p * v) :
    dyadicAtomFrequency j p i < (v : ℝ) / 2 ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnum : 2 * (i : ℝ) + 1 < 2 * ((p : ℝ) * v) := by
    exact_mod_cast (show 2 * i + 1 < 2 * (p * v) by omega)
  have hh := mul_lt_mul_of_pos_right hnum (show (0 : ℝ) < 2 ^ j by positivity)
  unfold dyadicAtomFrequency
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  rw [pow_succ]
  nlinarith only [hh]

theorem belovMultiplicity_le_two_pow (j : ℕ) : belovMultiplicity j ≤ 2 ^ j := by
  apply (belovMultiplicity_le j).trans
  have h : j < 2 ^ j := Nat.lt_two_pow_self
  omega

theorem belovFrequency_pos (q : ℕ) (a : BelovFamilyIndex q) : 0 < belovFrequency q a := by
  cases a with
  | inl _ => norm_num [belovFrequency]
  | inr a =>
    exact dyadicAtomFrequency_pos a.1 a.2.1 a.2.2
      ((Finset.mem_Icc.mp (belovLevelPrimes_subset q a.1 a.2.1.property)).1)

theorem belovFrequency_le_one (q : ℕ) (a : BelovFamilyIndex q) : belovFrequency q a ≤ 1 := by
  cases a with
  | inl _ => norm_num [belovFrequency]
  | inr a =>
    have hp := (Finset.mem_Icc.mp (belovLevelPrimes_subset q a.1 a.2.1.property)).1
    have h := dyadicAtomFrequency_lt_multiplicity a.1 a.2.1 (belovMultiplicity a.1)
      a.2.2 hp a.2.2.isLt
    have hm : (belovMultiplicity a.1 : ℝ) ≤ 2 ^ a.1 := by
      exact_mod_cast belovMultiplicity_le_two_pow a.1
    exact h.le.trans ((div_le_one (by positivity : (0 : ℝ) < 2 ^ a.1)).mpr hm)

theorem belovDenominator_pos (q : ℕ) (a : BelovFamilyIndex q) : 0 < belovDenominator q a :=
  inv_pos.mpr (belovFrequency_pos q a)

theorem one_le_belovDenominator (q : ℕ) (a : BelovFamilyIndex q) : 1 ≤ belovDenominator q a :=
  (one_le_inv₀ (belovFrequency_pos q a)).mpr (belovFrequency_le_one q a)

theorem belovDenominator_base (q : ℕ) : belovDenominator q (.inl ()) = 1 := by
  simp [belovDenominator, belovFrequency]

theorem inv_belovDenominator (q : ℕ) (a : BelovFamilyIndex q) :
    (belovDenominator q a)⁻¹ = belovFrequency q a := by
  simp [belovDenominator]

theorem summable_belovFrequency (q : ℕ) : Summable (belovFrequency q) := by
  apply Summable.sum
  · exact Summable.of_finite
  · exact summable_dyadicFrequency (belovLevelPrimes q) belovMultiplicity q
      (belovLevelPrimes_subset q) belovMultiplicity_le

theorem summable_inv_belovDenominator (q : ℕ) :
    Summable (fun a => (belovDenominator q a)⁻¹) := by
  simpa only [inv_belovDenominator] using summable_belovFrequency q

theorem summable_belovSineFamily (q : ℕ) (x : ℝ) :
    Summable (fun a => Real.sin (Real.pi * x / belovDenominator q a)) := by
  have h := (summable_belovFrequency q).mul_left (Real.pi * |x|)
  apply h.of_norm_bounded
  intro a
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |Real.pi * x / belovDenominator q a| := Real.abs_sin_le_abs
    _ = Real.pi * |x| * belovFrequency q a := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (belovDenominator_pos q a),
        div_eq_mul_inv, inv_belovDenominator]

theorem tsum_belovSineFamily (q : ℕ) (x : ℝ) :
    (∑' a, Real.sin (Real.pi * x / belovDenominator q a)) = belovSineTotal q x := by
  have hl : Summable ((fun a => Real.sin (Real.pi * x / belovDenominator q a)) ∘ Sum.inl) :=
    Summable.of_finite
  have hr : Summable ((fun a => Real.sin (Real.pi * x / belovDenominator q a)) ∘ Sum.inr) := by
    change Summable (fun a => Real.sin (Real.pi * x /
      (dyadicFrequency (belovLevelPrimes q) belovMultiplicity a)⁻¹))
    simpa only [div_eq_mul_inv, inv_inv]
      using summable_sine_dyadicFrequency (belovLevelPrimes q) belovMultiplicity q x
        (belovLevelPrimes_subset q) belovMultiplicity_le
  rw [Summable.tsum_sum hl hr]
  have heq := tsum_sine_dyadicFrequency (belovLevelPrimes q) belovMultiplicity q x
    (belovLevelPrimes_subset q) belovMultiplicity_le
  simpa only [belovDenominator, belovFrequency, div_eq_mul_inv, inv_inv, mul_one,
    tsum_fintype, Fintype.sum_unique, belovSineTotal, belovSineLevel] using
    congrArg (fun y => Real.sin (Real.pi * x) + y) heq

theorem belovSineFamily_pos_small (q : ℕ) (hq : 3 ≤ q) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < ∑' a, Real.sin (Real.pi * x / belovDenominator q a) := by
  rw [tsum_belovSineFamily]
  exact belovSineTotal_pos_small q hq hx hx1

end Erdos345
