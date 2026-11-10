import Erdos345.CosineHalfPeriodExtension
import Erdos345.CountingProfileWeights
import Erdos345.PublishedInputAssembly

namespace Erdos345

/-- A direct, deliberately nonsharp positivity transfer. The global sine
positivity is still an explicit hypothesis. No source theorem is assumed. -/
theorem belov_profile_cosine_of_global_sine (q : ℕ)
    (hglobal : ∀ x : ℝ, 0 ≤ x → 0 ≤ belovSineTotal q x) (m : ℕ) :
    ∀ θ : ℝ, 0 ≤ 2 * belovProfileMajorant q m + ∑ i ∈ Finset.range m,
      (countingProfileWeight (belovCountingProfile q) m i : ℝ) *
        Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
  apply cosine_nonneg_of_half_period
  intro θ hθ hπ
  have hs : 0 ≤ ∑' a : BelovFamilyIndex q,
      Real.sin (((m : ℝ) / belovDenominator q a) * θ) := by
    have heq : (∑' a : BelovFamilyIndex q,
        Real.sin (((m : ℝ) / belovDenominator q a) * θ)) =
        belovSineTotal q ((m : ℝ) * θ / Real.pi) := by
      simp_rw [belov_scaled_sine_identity]
      exact tsum_belovSineFamily q ((m : ℝ) * θ / Real.pi)
    rw [heq]
    apply hglobal
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg m) hθ) Real.pi_pos.le
  exact profile_cosine_nonneg_of_sine_nonneg q m θ hθ hπ hs

/-- The concrete family has all required finite/profile structure. The
two remaining analytic obligations are global sine positivity and this
quantitative profile budget; neither is asserted here. -/
theorem belov_input_of_concrete_sine_profile (q : ℕ)
    (hglobal : ∀ x : ℝ, 0 ≤ x → 0 ≤ belovSineTotal q x)
    (hbudget : ∀ N : ℕ, 0 < N →
      belovProfileMajorant q N ≤ (2 : ℝ) ^ 29 * (1 + Real.log (N : ℝ)) ^ 5) :
    BelovKonyaginInput := by
  intro N hN
  obtain ⟨w, a, hw, hmass, hpos, ha⟩ := exact_mass_from_counting_profile N hN
    (belovCountingProfile q) (belovCountingProfile_monotone q)
    (fun _ hx => belovCountingProfile_zero_below_one q hx) (belovCountingProfile_one_pos q)
    (fun m => 2 * belovProfileMajorant q m) (2 * belovProfileMajorant q N)
    (fun m _ => belov_profile_cosine_of_global_sine q hglobal m)
    (fun m hm => mul_le_mul_of_nonneg_left (belovProfileMajorant_monotone q hm) (by norm_num))
  refine ⟨w, a, hw, hmass, hpos, ?_⟩
  have hc := belovCountingProfile_le_majorant q N
  have hb := hbudget N hN
  have hL : 0 ≤ (1 + Real.log (N : ℝ)) ^ 5 := by
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  norm_num at hb ⊢
  nlinarith

/-- Exact original target, conditional on the two concrete sine-profile
estimates and the still-unformalized shifted-prime theorem. -/
theorem intended_of_concrete_sine_profile_and_fan (q : ℕ)
    (hglobal : ∀ x : ℝ, 0 ≤ x → 0 ≤ belovSineTotal q x)
    (hbudget : ∀ N : ℕ, 0 < N →
      belovProfileMajorant q N ≤ (2 : ℝ) ^ 29 * (1 + Real.log (N : ℝ)) ^ 5)
    (hfan : FanPollackInput) : IntendedStatement :=
  intended_of_published_analytic_inputs
    (belov_input_of_concrete_sine_profile q hglobal hbudget) hfan

end Erdos345
