import Erdos345.JointGroupSelection
import Erdos345.ReservedBases

namespace Erdos345

open Filter

theorem eventually_reserve_large : ∀ᶠ k : ℕ in atTop, 2048 * k ≤ fourierN k := by
  filter_upwards [eventually_monomial_exp_dominated 1 0 0 2048 (by norm_num)] with k hk
  simp only [pow_one, pow_zero, zero_mul, Real.exp_zero, mul_one] at hk
  have hA : 0 ≤ logScale k ^ 8 := by positivity
  have hN : (2048 : ℝ) * k ≤ fourierN k := hk.trans
    ((Real.exp_le_exp.mpr (by linarith : logScale k ^ 8 / 4 ≤ logScale k ^ 8)).trans (fourierN_bounds k).1)
  exact_mod_cast hN

/-- The selected groups are simultaneously disjoint and span-bounded,
and each is good for at least half of the actual reserved bases. The
only unproved source premise is the stated cosine existence theorem. -/
theorem good_degrees_reserved_groups
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧ 2048 * k ≤ fourierN k ∧
      ∃ G : Fin 128 → Finset ℕ,
        (∀ j, G j ⊆ unreservedPopulation (fourierN k) k) ∧
        (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧
        (∀ j, (∑ n ∈ G j, (n : ℝ) ^ k) <
          4 * ((fourierN k : ℝ) ^ (k + 1) / ((8192 : ℝ) * k))) ∧
        (∀ j, (reserveCount (fourierN k) k : ℝ) / 2 ≤
          (((reservedBases (fourierN k) k).filter (fun c =>
            ((c ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues (G j) k (c ^ k)).card)).card : ℝ)) := by
  classical
  obtain ⟨K₁, hK₁⟩ := good_degrees_selected_groups hinput
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp eventually_reserve_large
  refine ⟨max 20 (max K₁ K₂), ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hgroups⟩ := hK₁ Y (by omega)
  have hk20 : 20 ≤ k := by omega
  have hlarge : 2048 * k ≤ fourierN k := hK₂ k (by omega)
  have hk0 : 0 < k := by omega
  have hreserve : (reservedBases (fourierN k) k).Nonempty :=
    reservedBases_nonempty (fourierN k) k hk0 (by omega)
  obtain ⟨G, hsub, hdisj, hspan, hgood⟩ := hgroups (reservedBases (fourierN k) k) hreserve
    (fun c hc => reservedBases_positive (fourierN k) k c hc)
  refine ⟨k, hkY, hk2Y, hk20, hlarge, G, hsub, hdisj, hspan, ?_⟩
  intro j
  simpa only [reservedBases_card] using hgood j

end Erdos345
