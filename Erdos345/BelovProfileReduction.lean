import Erdos345.CountingProfileWeights
import Erdos345.PublishedInputAssembly

namespace Erdos345

/-- Reduction of the needed cosine theorem to the counting profile and
base-polynomial estimates in the cited construction. Analytic positivity
and the profile estimate remain explicit obligations. -/
theorem belov_input_of_profile_data (φ : ℝ → ℕ) (F : ℕ → ℝ)
    (hφ : Monotone φ) (hφzero : ∀ x : ℝ, x < 1 → φ x = 0) (hφone : 1 ≤ φ 1)
    (hF : Monotone F)
    (hφF : ∀ N : ℕ, 0 < N → (φ (N : ℝ) : ℝ) ≤ F N)
    (hdouble : ∀ N : ℕ, 0 < N → F (2 * N) ≤ 2 * F N)
    (hbudget : ∀ N : ℕ, 0 < N → F N ≤ (2 : ℝ) ^ 29 * (1 + Real.log (N : ℝ)) ^ 5)
    (hbase : ∀ m : ℕ, ∀ θ : ℝ, 0 ≤ (11 / 10 : ℝ) * F (2 * m) +
      ∑ i ∈ Finset.range m, (countingProfileWeight φ m i : ℝ) *
        Real.cos (((i + 1 : ℕ) : ℝ) * θ)) : BelovKonyaginInput := by
  intro N hN
  have hcost : ∀ m ≤ N, (11 / 10 : ℝ) * F (2 * m) ≤ (11 / 5 : ℝ) * F N := by
    intro m hm
    have hFm := hF (show 2 * m ≤ 2 * N by omega)
    have hd := hdouble N hN
    linarith
  obtain ⟨w, a, hanti, hmass, hpos, ha⟩ := exact_mass_from_counting_profile N hN φ hφ hφzero hφone
    (fun m => (11 / 10 : ℝ) * F (2 * m)) ((11 / 5 : ℝ) * F N)
    (fun m _ => hbase m) hcost
  refine ⟨w, a, hanti, hmass, hpos, ?_⟩
  have hp := hφF N hN
  have hb := hbudget N hN
  have hF0 : 0 ≤ F N := (Nat.cast_nonneg (φ (N : ℝ))).trans hp
  have hL0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ 5 := by
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  norm_num at hb ⊢
  nlinarith

end Erdos345
