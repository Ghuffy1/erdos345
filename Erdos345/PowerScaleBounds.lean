import Erdos345.PowerPhaseScale

namespace Erdos345

theorem positivePhaseScale_ge (q h k : ℕ) (hq : 0 < q) (hh : 0 < h) (hk : 0 < k)
    (s : ℝ) (hs : 0 ≤ s) (hbudget : (h : ℝ) * s ^ k ≤ q) :
    s ≤ positivePhaseScale q h k := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  apply (pow_le_pow_iff_left₀ hs (positivePhaseScale_pos q h k hq hh).le (Nat.ne_of_gt hk)).mp
  rw [positivePhaseScale_pow q h k hq hh hk]
  exact (le_div_iff₀ hhR).mpr (by nlinarith only [hbudget])

theorem positivePhaseScale_le (q h k : ℕ) (hq : 0 < q) (hh : 0 < h) (hk : 0 < k)
    (s : ℝ) (hs : 0 ≤ s) (hbudget : (q : ℝ) ≤ h * s ^ k) :
    positivePhaseScale q h k ≤ s := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  apply (pow_le_pow_iff_left₀ (positivePhaseScale_pos q h k hq hh).le hs (Nat.ne_of_gt hk)).mp
  rw [positivePhaseScale_pow q h k hq hh hk]
  exact (div_le_iff₀ hhR).mpr (by nlinarith only [hbudget])

theorem positivePhaseScale_le_base (c h k : ℕ) (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) :
    positivePhaseScale (c ^ k) h k ≤ c := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  apply positivePhaseScale_le (c ^ k) h k (pow_pos hc _) hh hk (c : ℝ) (Nat.cast_nonneg _)
  have hp : 0 ≤ (c : ℝ) ^ k := by positivity
  simpa only [Nat.cast_pow, one_mul] using mul_le_mul_of_nonneg_right hhR hp

end Erdos345
