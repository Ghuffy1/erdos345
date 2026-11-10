import Erdos345.ExplicitCenterWindow
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos345

noncomputable def logScale (k : ℕ) : ℝ := 1 + Real.log ((2 * k : ℕ) : ℝ)

theorem logScale_ge_one (k : ℕ) (hk : 0 < k) : 1 ≤ logScale k := by
  have h : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  exact le_add_of_nonneg_right h

theorem natLog_two_le_real_log (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
  Real.natLog_le_logb n 2

theorem conductorCoefficient_le_logScale (k : ℕ) (hk : 0 < k) :
    conductorCoefficient (k + 1) k ≤
      3 * (1 / Real.log 2 + 5) ^ 2 * logScale k ^ 2 := by
  let K := logScale k
  let A := 1 / Real.log 2 + 5
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hNlog : Real.log ((k + 1 : ℕ) : ℝ) ≤ K := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
      (show ((k + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k + 1 ≤ 2 * k by omega))
    change _ ≤ 1 + Real.log ((2 * k : ℕ) : ℝ)
    linarith
  have hklog : Real.log (k : ℝ) ≤ K := by
    have h := Real.log_le_log (by exact_mod_cast hk)
      (show (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ k)
    exact h.trans hNlog
  have hN : (Nat.log 2 (k + 1) : ℝ) ≤ K / Real.log 2 :=
    (natLog_two_le_real_log (k + 1)).trans (div_le_div_of_nonneg_right hNlog hlog2.le)
  have hn : (Nat.log 2 k : ℝ) ≤ K / Real.log 2 :=
    (natLog_two_le_real_log k).trans (div_le_div_of_nonneg_right hklog hlog2.le)
  have hcommon : K / Real.log 2 + 5 ≤ A * K := by
    dsimp only [A]
    simp only [div_eq_mul_inv, one_mul]
    nlinarith
  have hA5 : (Nat.log 2 (k + 1) : ℝ) + 5 ≤ A * K := by linarith
  have hA1 : (Nat.log 2 (k + 1) : ℝ) + 1 ≤ A * K := by linarith
  have hB1 : (Nat.log 2 k : ℝ) + 1 ≤ A * K := by linarith
  have hprodA := mul_le_mul hA1 hA5 (by positivity : 0 ≤ (Nat.log 2 (k + 1) : ℝ) + 5)
    (mul_nonneg hA (by linarith : 0 ≤ K))
  have hprodB := mul_le_mul hA1 hB1 (by positivity : 0 ≤ (Nat.log 2 k : ℝ) + 1)
    (mul_nonneg hA (by linarith : 0 ≤ K))
  unfold conductorCoefficient
  change _ ≤ 3 * A ^ 2 * K ^ 2
  nlinarith

theorem goodConductorEnvelope_le_logScale (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k) :
    goodConductorEnvelope Y k ≤ (4 / Real.log 2 + 12) * logScale k ^ 3 := by
  let K := logScale k
  let A := 1 / Real.log 2 + 2
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK0 : 0 ≤ K := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hlog2k : Real.log ((2 * k : ℕ) : ℝ) ≤ K := by dsimp only [K, logScale]; linarith
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogkK : Real.log (k : ℝ) ≤ K :=
    (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast (show k ≤ 2 * k by omega))).trans hlog2k
  have hlogk1 : Real.log ((k + 1 : ℕ) : ℝ) ≤ K :=
    (Real.log_le_log (by positivity) (by exact_mod_cast (show k + 1 ≤ 2 * k by omega))).trans hlog2k
  have hnum : (Nat.log 2 (2 * Y) : ℝ) ≤ K / Real.log 2 := by
    have hnat : Nat.log 2 (2 * Y) ≤ Nat.log 2 (2 * k) := Nat.log_mono_right (by omega)
    exact (show (Nat.log 2 (2 * Y) : ℝ) ≤ Nat.log 2 (2 * k) by exact_mod_cast hnat).trans
      ((natLog_two_le_real_log (2 * k)).trans (div_le_div_of_nonneg_right hlog2k hlog2.le))
  have hcoef : ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) ≤ A * K := by
    push_cast
    dsimp only [A]
    simp only [div_eq_mul_inv, one_mul] at hnum ⊢
    nlinarith
  have hhar0 : 0 ≤ (harmonic (2 * Y) : ℝ) := by exact_mod_cast harmonic_nonneg (2 * Y)
  have hhar : (harmonic (2 * Y) : ℝ) ≤ K := by
    refine (harmonic_le_one_add_log (2 * Y)).trans ?_
    by_cases hY : Y = 0
    · subst Y
      simp only [mul_zero, Nat.cast_zero, Real.log_zero, add_zero]
      exact hK
    · have hlog := Real.log_le_log
        (show (0 : ℝ) < ((2 * Y : ℕ) : ℝ) by exact_mod_cast (show 0 < 2 * Y by omega))
        (show ((2 * Y : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show 2 * Y ≤ 2 * k by omega))
      change _ ≤ 1 + Real.log ((2 * k : ℕ) : ℝ)
      linarith
  have hmain : 4 * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) *
      (harmonic (2 * Y) : ℝ) * Real.log (k : ℝ) ≤ 4 * A * K ^ 3 := by
    calc
      _ ≤ 4 * (A * K) * K * K := by gcongr
      _ = _ := by ring
  have hKcube : K ≤ K ^ 3 := by
    have hpow := pow_le_pow_right₀ hK (by decide : 1 ≤ (3 : ℕ))
    simpa only [pow_one] using hpow
  unfold goodConductorEnvelope
  change _ ≤ (4 / Real.log 2 + 12) * K ^ 3
  dsimp only [A] at hmain
  simp only [div_eq_mul_inv, one_mul] at hmain ⊢
  nlinarith

end Erdos345
