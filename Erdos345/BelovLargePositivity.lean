import Erdos345.BelovNegativeLevels
import Erdos345.BelovSafeLevels
import Erdos345.PrimeMassLower

namespace Erdos345

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem belovSineLevel_small_lower (q r : ℕ) {x : ℝ} (hx : 0 < x)
    (hsafe : (belovMultiplicity r : ℝ) * (x / 2 ^ r) ≤ 1) :
    (2 / Real.pi * (belovMultiplicity r : ℝ) ^ 2 * (x / 2 ^ r)) *
      (∑ p ∈ belovLevelPrimes q r, (p : ℝ)) ≤ belovSineLevel q r x := by
  change _ ≤ ∑ p ∈ belovLevelPrimes q r, scaledSineBlock p (belovMultiplicity r) (x / 2 ^ r)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have h := scaledSineBlock_small_lower p (belovMultiplicity r) (belovLevelPrimes_prime hp).pos
    (belovMultiplicity_pos r) (show 0 < x / 2 ^ r by positivity) hsafe
  convert h using 1
  ring

theorem belov_scale_512_le_multiplicity (r : ℕ) :
    Real.log ((512 * (r + 1) ^ 2 : ℕ) : ℝ) ≤ 14 * (belovMultiplicity r : ℝ) := by
  have hl : 0 ≤ Real.log ((r + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r + 1 by omega))
  have hv1 : (1 : ℝ) ≤ belovMultiplicity r := by exact_mod_cast belovMultiplicity_pos r
  have hvlog : Real.log ((r + 1 : ℕ) : ℝ) < (belovMultiplicity r : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log ((r + 1 : ℕ) : ℝ))
    unfold belovMultiplicity
    push_cast at h ⊢
    linarith
  have h512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
  have heq : Real.log ((512 * (r + 1) ^ 2 : ℕ) : ℝ) =
      9 * Real.log 2 + 2 * Real.log ((r + 1 : ℕ) : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, h512]
    norm_num
  rw [heq]
  have htwo : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  nlinarith

theorem belovSineLevel_balanced_lower (r : ℕ) (hr : 5 ≤ r) {x : ℝ} (hx : 0 < x)
    (hhalf : 1 / 2 ≤ (belovMultiplicity r : ℝ) * (x / 2 ^ r))
    (hsafe : (belovMultiplicity r : ℝ) * (x / 2 ^ r) ≤ 1) :
    184 * ((r : ℝ) + 1) ^ 4 ≤ belovSineLevel 512 r x := by
  let N := 512 * (r + 1) ^ 2
  have hN : 16384 ≤ N := by dsimp only [N]; nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm := belov_prime_mass_lower 512 r hN
  have hs := belovSineLevel_small_lower 512 r hx hsafe
  have hS0 : 0 ≤ ∑ p ∈ belovLevelPrimes 512 r, (p : ℝ) := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg p)
  have hcoef : 0 ≤ 2 / Real.pi * (belovMultiplicity r : ℝ) *
      (∑ p ∈ belovLevelPrimes 512 r, (p : ℝ)) :=
    mul_nonneg (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)) hS0
  have hlevel : (belovMultiplicity r : ℝ) / Real.pi *
      (∑ p ∈ belovLevelPrimes 512 r, (p : ℝ)) ≤ belovSineLevel 512 r x := by
    calc
      _ = (2 / Real.pi * (belovMultiplicity r : ℝ) * (∑ p ∈ belovLevelPrimes 512 r, (p : ℝ))) * (1 / 2) := by ring
      _ ≤ (2 / Real.pi * (belovMultiplicity r : ℝ) * (∑ p ∈ belovLevelPrimes 512 r, (p : ℝ))) *
          ((belovMultiplicity r : ℝ) * (x / 2 ^ r)) := mul_le_mul_of_nonneg_left hhalf hcoef
      _ = _ := by ring
      _ ≤ _ := hs
  have hratio : (1 / 14 : ℝ) ≤ (belovMultiplicity r : ℝ) / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    have hh := belov_scale_512_le_multiplicity r
    change Real.log (N : ℝ) ≤ 14 * (belovMultiplicity r : ℝ) at hh
    linarith
  have hbound : (N : ℝ) ^ 2 / (350 * Real.pi) ≤ belovSineLevel 512 r x := by
    calc
      _ = (1 / 14 : ℝ) * ((N : ℝ) ^ 2 / (25 * Real.pi)) := by ring
      _ ≤ ((belovMultiplicity r : ℝ) / Real.log (N : ℝ)) * ((N : ℝ) ^ 2 / (25 * Real.pi)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = ((belovMultiplicity r : ℝ) / Real.pi) * ((N : ℝ) ^ 2 / (25 * Real.log (N : ℝ))) := by ring
      _ ≤ ((belovMultiplicity r : ℝ) / Real.pi) * (∑ p ∈ belovLevelPrimes 512 r, (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hm (div_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
      _ ≤ _ := hlevel
  have hnum : 184 * ((r : ℝ) + 1) ^ 4 ≤ (N : ℝ) ^ 2 / (350 * Real.pi) := by
    apply (le_div_iff₀ (show 0 < 350 * Real.pi by positivity)).mpr
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le
      (show 0 ≤ ((r : ℝ) + 1) ^ 4 by positivity)
    have hNcast : (N : ℝ) ^ 2 = 262144 * ((r : ℝ) + 1) ^ 4 := by
      dsimp only [N]
      push_cast
      ring
    rw [hNcast]
    nlinarith only [hpi, pow_nonneg (show 0 ≤ (r : ℝ) + 1 by positivity) 4]
  exact hnum.trans hbound

theorem belovSineTotal_pos_large {x : ℝ} (hx : 8 < x) : 0 < belovSineTotal 512 x := by
  obtain ⟨r, hr, hxr, hhalf, hsafe⟩ := exists_belov_balanced_level hx
  have hx0 : 0 < x := by linarith
  have hlevel := belovSineLevel_balanced_lower r hr hx0 hhalf hsafe
  have htotal := belovSineTotal_lower_with_level 512 r (by norm_num) hx0.le hxr
  have htwo : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hpoly : (r : ℝ) * (r + 1) ^ 2 * (r + 2) ≤ ((r : ℝ) + 1) ^ 4 := by
    nlinarith only [sq_nonneg ((r : ℝ) + 1)]
  have hp0 : 0 ≤ (r : ℝ) * (r + 1) ^ 2 * (r + 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_right htwo hp0
  have hpow : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 :=
    one_le_pow₀ (by have hh := Nat.cast_nonneg (α := ℝ) r; linarith)
  norm_num at htotal
  nlinarith only [htotal, hlevel, hmul, hpoly, hpow]

theorem belovSineTotal_nonneg_512 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ belovSineTotal 512 x := by
  by_cases hzero : x = 0
  · subst x
    simp [belovSineTotal, belovSineLevel, dyadicSineLevel, scaledSineBlock, oddSineSum]
  have hxpos : 0 < x := by positivity
  by_cases hx8 : x ≤ 8
  · exact (belovSineTotal_pos_upto_eight 512 (by norm_num) hxpos hx8).le
  · exact (belovSineTotal_pos_large (lt_of_not_ge hx8)).le

end Erdos345
