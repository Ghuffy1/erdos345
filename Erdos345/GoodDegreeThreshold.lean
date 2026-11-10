import Erdos345.RepresentedIntervalSelection
import Erdos345.RadixCompleteness

namespace Erdos345

/-- The full upper-bound construction, including its infinite tail.
The only remaining input here is the displayed cosine existence theorem. -/
theorem good_degrees_threshold_upper
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧
      leastPowerThreshold k ≤ 256 * (fourierN k) ^ (k + 1) := by
  obtain ⟨K, hK⟩ := good_degrees_represented_interval hinput
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨k, a, L, hkY, hk2Y, hk20, hkN, hI, hL, ha⟩ := hK Y hY
  have hthreshold := threshold_of_representedInterval (by omega : 0 < k) hI hL hkN
  have hleast := (leastPowerThreshold_spec k (by omega)).2 hthreshold
  exact ⟨k, hkY, hk2Y, hk20, hleast.trans ha⟩

end Erdos345
