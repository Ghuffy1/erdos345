import Erdos345.FiniteCenterCriterion

namespace Erdos345

theorem factorial_conductor_log_bound (q k : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hdiv : q ∣ k.factorial * (k + 1).factorial) :
    Real.log (q : ℝ) ≤ 3 * (k : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by
  have hfirst : k.factorial ≤ (k + 1) ^ k :=
    k.factorial_le_pow.trans (Nat.pow_le_pow_left (Nat.le_succ k) k)
  have hprod : k.factorial * (k + 1).factorial ≤ (k + 1) ^ (k + (k + 1)) := by
    rw [pow_add]
    exact Nat.mul_le_mul hfirst (k + 1).factorial_le_pow
  have hpow : (k + 1) ^ (k + (k + 1)) ≤ (k + 1) ^ (3 * k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hqpow : q ≤ (k + 1) ^ (3 * k) :=
    (Nat.le_of_dvd (mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) hdiv).trans (hprod.trans hpow)
  have hlog := Real.log_le_log (by exact_mod_cast hq) (show (q : ℝ) ≤ ((k + 1) ^ (3 * k) : ℕ) by exact_mod_cast hqpow)
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hlog

noncomputable def goodConductorEnvelope (Y k : ℕ) : ℝ :=
  Real.log ((2 * k : ℕ) : ℝ) +
    4 * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) * (harmonic (2 * Y) : ℝ) * Real.log (k : ℝ) +
    3 * Real.log ((k + 1 : ℕ) : ℝ)

theorem goodConductorEnvelope_nonneg (Y k : ℕ) (hk : 0 < k) :
    0 ≤ goodConductorEnvelope Y k := by
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogk1 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  have hlog2k : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  have hhar : 0 ≤ (harmonic (2 * Y) : ℝ) := by exact_mod_cast harmonic_nonneg (2 * Y)
  unfold goodConductorEnvelope
  positivity

/-- The elementary simultaneous good-degree theorem supplies an envelope
for every exact reduction, including degree k for factorial conductors. -/
theorem exists_good_conductor_degree (Y : ℕ) (hY : 0 < Y) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ q : ℕ, 0 < q → q ∣ k.factorial * (k + 1).factorial →
        ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d →
          Real.log (q : ℝ) ≤ goodConductorEnvelope Y k * d := by
  obtain ⟨k, hkY, hk2Y, hgood⟩ := exists_good_reduction_degree Y hY
  have hk : 0 < k := hY.trans_le hkY
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogk1 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  have hlog2k : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  have hhar : 0 ≤ (harmonic (2 * Y) : ℝ) := by exact_mod_cast harmonic_nonneg (2 * Y)
  have hrest : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) +
      4 * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℝ) * (harmonic (2 * Y) : ℝ) * Real.log (k : ℝ) := by positivity
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro q hq hdiv
  apply log_bound_for_all_reductions q k hq (goodConductorEnvelope Y k)
  · have h := factorial_conductor_log_bound q k hq hk hdiv
    unfold goodConductorEnvelope
    have hmul := mul_nonneg hrest (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  · intro d hd hdk
    have h := hgood d hd hdk
    unfold goodConductorEnvelope
    have hmul := mul_nonneg hlogk1 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    nlinarith

end Erdos345
