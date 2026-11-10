import Erdos345.BelovProfileTail
import Erdos345.ConcreteProfileBridge

namespace Erdos345

def belovProfileCut (N : ℕ) : ℕ := Nat.log 2 N + 2

theorem belovProfileCut_ge_three (N : ℕ) (hN : 2 ≤ N) : 3 ≤ belovProfileCut N := by
  have h : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) (by simpa using hN)
  unfold belovProfileCut
  omega

theorem belovProfileCut_power_bound (N : ℕ) :
    (N : ℝ) / 2 ^ belovProfileCut N ≤ 1 / 2 := by
  have h : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by decide) N
  have hR : (N : ℝ) ≤ 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h.le
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ belovProfileCut N)).mpr
  unfold belovProfileCut
  calc
    _ ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := hR
    _ = (1 / 2 : ℝ) * 2 ^ (Nat.log 2 N + 2) := by rw [show Nat.log 2 N + 2 = (Nat.log 2 N + 1) + 1 by omega, pow_succ]; ring

theorem belovProfileCut_log_bound (N : ℕ) (hN : 0 < N) :
    (belovProfileCut N : ℝ) ≤ 2 * (1 + Real.log (N : ℝ)) := by
  have hpow := Nat.pow_log_le_self 2 hN.ne'
  have hpowR : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast hpow
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 N) hpowR
  rw [Real.log_pow] at h
  have hh := mul_le_mul_of_nonneg_left log_two_profile_bounds.1
    (Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ Nat.log 2 N)
  unfold belovProfileCut
  push_cast
  linarith

theorem belovProfile_cut_bound (q N : ℕ) (hq : 256 ≤ q) (hN : 2 ≤ N) :
    belovProfileMajorant q N ≤ 64 * (q : ℝ) ^ 2 * (belovProfileCut N : ℝ) ^ 5 := by
  let r := belovProfileCut N
  have hr : 3 ≤ r := belovProfileCut_ge_three N hN
  have hb := belovProfile_split_bound q N r hq hr
  have hc : (N : ℝ) / 2 ^ r ≤ 1 / 2 := belovProfileCut_power_bound N
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by omega))
  have hr5 : (1 : ℝ) ≤ (r : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ r by omega))
  have hp : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (r : ℝ) ^ 5 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr hr5)]
  have ht : ((5 / 3 : ℝ) * (q : ℝ) ^ 2 * (N : ℝ) / 2 ^ r) * (36 * (r : ℝ) ^ 5) ≤
      30 * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 := by
    have hh := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (60 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 by positivity)
    calc
      _ = (60 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 * ((N : ℝ) / 2 ^ r) := by ring
      _ ≤ (60 : ℝ) * (q : ℝ) ^ 2 * (r : ℝ) ^ 5 * (1 / 2) := hh
      _ = _ := by ring
  change belovProfileMajorant q N ≤ 64 * (q : ℝ) ^ 2 * (r : ℝ) ^ 5
  nlinarith

theorem belovProfileMajorant_log_bound (q N : ℕ) (hq : 256 ≤ q) (hN : 0 < N) :
    belovProfileMajorant q N ≤ 2048 * (q : ℝ) ^ 2 * (1 + Real.log (N : ℝ)) ^ 5 := by
  by_cases hN1 : N = 1
  · subst N
    have hb := belovProfile_linear_bound q 1 hq
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by omega))
    norm_num at hb ⊢
    nlinarith
  · have hN2 : 2 ≤ N := by omega
    have hb := belovProfile_cut_bound q N hq hN2
    have hc := pow_le_pow_left₀ (Nat.cast_nonneg (belovProfileCut N)) (belovProfileCut_log_bound N hN) 5
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 64 * (q : ℝ) ^ 2 by positivity)
    calc
      _ ≤ 64 * (q : ℝ) ^ 2 * (belovProfileCut N : ℝ) ^ 5 := hb
      _ ≤ 64 * (q : ℝ) ^ 2 * (2 * (1 + Real.log (N : ℝ))) ^ 5 := hm
      _ = _ := by ring

theorem belovProfile_budget_512 (N : ℕ) (hN : 0 < N) :
    belovProfileMajorant 512 N ≤ (2 : ℝ) ^ 29 * (1 + Real.log (N : ℝ)) ^ 5 := by
  have h := belovProfileMajorant_log_bound 512 N (by decide) hN
  norm_num at h ⊢
  exact h

theorem belov_input_of_global_sine_512
    (hglobal : ∀ x : ℝ, 0 ≤ x → 0 ≤ belovSineTotal 512 x) : BelovKonyaginInput :=
  belov_input_of_concrete_sine_profile 512 hglobal belovProfile_budget_512

theorem intended_of_global_sine_512_and_fan
    (hglobal : ∀ x : ℝ, 0 ≤ x → 0 ≤ belovSineTotal 512 x)
    (hfan : FanPollackInput) : IntendedStatement :=
  intended_of_published_analytic_inputs (belov_input_of_global_sine_512 hglobal) hfan

end Erdos345
