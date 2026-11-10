import Erdos345.FourierDecay

namespace Erdos345

open Filter
open scoped Topology

theorem tendsto_fourier_decay_zero :
    Tendsto (fun k : ℕ => Real.exp (-(k : ℝ) * logScale k ^ 8)) atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℕ => (k : ℝ) * logScale k ^ 8) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (show Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hK : 1 ≤ logScale k ^ 8 := one_le_pow₀ (logScale_ge_one k (by omega))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℝ) k)
  simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hg

theorem eventually_fourier_decay_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, Real.exp (-(k : ℝ) * logScale k ^ 8) < ε :=
  tendsto_fourier_decay_zero.eventually (gt_mem_nhds hε)

/-- Given the cosine existence theorem, the collision sums can be made
uniformly smaller than any positive tolerance at a degree in each
sufficiently large dyadic interval. -/
theorem good_degrees_collision_small
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ c : ℕ, 0 < c → c ≤ fourierN k →
        powerCollisionSum (unreservedPopulation (fourierN k) k) k (c ^ k) (fourierT k) < ε := by
  obtain ⟨K₁, hK₁⟩ := good_degrees_fourier_decay hinput
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (eventually_fourier_decay_small ε hε)
  refine ⟨max K₁ K₂, ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hdecay⟩ := hK₁ Y (by omega)
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro c hc hcN
  exact (hdecay c hc hcN).trans_lt (hK₂ k (by omega))

end Erdos345
