import Erdos345.AugmentedGroupBounds
import Mathlib.Data.Nat.GCD.Basic

namespace Erdos345

def auxiliaryPair (j : Fin 128) : Finset ℕ := {2 * j.val + 2, 2 * j.val + 3}

theorem auxiliaryPair_subset (j : Fin 128) : auxiliaryPair j ⊆ Finset.Icc 2 257 := by
  intro n hn
  have hj := j.isLt
  simp only [auxiliaryPair, Finset.mem_insert, Finset.mem_singleton] at hn
  apply Finset.mem_Icc.mpr
  omega

theorem auxiliaryPair_disjoint (i j : Fin 128) (hij : i ≠ j) :
    Disjoint (auxiliaryPair i) (auxiliaryPair j) := by
  apply Finset.disjoint_left.mpr
  intro n hi hj
  simp only [auxiliaryPair, Finset.mem_insert, Finset.mem_singleton] at hi hj
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

theorem auxiliaryPair_powers_coprime (j : Fin 128) (k : ℕ) :
    Nat.Coprime ((2 * j.val + 2) ^ k) ((2 * j.val + 3) ^ k) := by
  apply Nat.Coprime.pow k k
  rw [Nat.coprime_iff_gcd_eq_one]
  have heq : 2 * j.val + 3 = 1 + (2 * j.val + 2) := by omega
  rw [heq, Nat.gcd_add_self_right, Nat.gcd_one_right]

theorem self_power_mem_finitePowerSums {G : Finset ℕ} {b : ℕ} (hb : b ∈ G) (k : ℕ) :
    b ^ k ∈ finitePowerSums G k := by
  apply Finset.mem_image.mpr
  refine ⟨{b}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hb), ?_⟩
  simp

/-- The two consecutive bases exclude every proper arithmetic
progression for the actual subset-sum set, including nonzero offsets. -/
theorem auxiliaryPair_no_proper_progression (G : Finset ℕ) (j : Fin 128) (k d a : ℕ)
    (h : ∀ n ∈ finitePowerSums (G ∪ auxiliaryPair j) k, n % d = a % d) : d = 1 := by
  have hzero := h 0 (zero_mem_finitePowerSums _ _)
  have hleft := h _ (self_power_mem_finitePowerSums
    (show 2 * j.val + 2 ∈ G ∪ auxiliaryPair j by simp [auxiliaryPair]) k)
  have hright := h _ (self_power_mem_finitePowerSums
    (show 2 * j.val + 3 ∈ G ∪ auxiliaryPair j by simp [auxiliaryPair]) k)
  have hl : d ∣ (2 * j.val + 2) ^ k := Nat.dvd_of_mod_eq_zero (hleft.trans hzero.symm)
  have hr : d ∣ (2 * j.val + 3) ^ k := Nat.dvd_of_mod_eq_zero (hright.trans hzero.symm)
  have hg := Nat.dvd_gcd hl hr
  rw [(auxiliaryPair_powers_coprime j k).gcd_eq_one] at hg
  exact Nat.dvd_one.mp hg

theorem reservedBases_auxiliary_disjoint (N k : ℕ) (hk : 20 ≤ k) (hN : 2048 * k ≤ N) :
    Disjoint (reservedBases N k) (Finset.Icc 2 257) := by
  apply Finset.disjoint_left.mpr
  intro n hn ha
  have hU := unreservedEndpoint_ge_three_quarters N k (by omega)
  have hnU : (unreservedEndpoint N k : ℝ) < n := by
    exact_mod_cast reservedBases_above_unreserved N k n hn
  have hnA : (n : ℝ) ≤ 257 := by exact_mod_cast (Finset.mem_Icc.mp ha).2
  have hNk : (2048 : ℝ) * k ≤ N := by exact_mod_cast hN
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem auxiliaryPair_span_le (N k : ℕ) (j : Fin 128) (hk : 2 ≤ k) (hN : 514 ≤ N) :
    (∑ n ∈ auxiliaryPair j, (n : ℝ) ^ k) ≤ (N : ℝ) ^ k / 2 := by
  have heach (n : ℕ) (hn : n ∈ auxiliaryPair j) : (n : ℝ) ^ k ≤ (N : ℝ) ^ k / 4 := by
    have hn257 := (Finset.mem_Icc.mp (auxiliaryPair_subset j hn)).2
    have hnN : (2 : ℝ) * n ≤ N := by exact_mod_cast (show 2 * n ≤ N by omega)
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 * n by positivity) hnN k
    have hfour : (4 : ℝ) ≤ 2 ^ k := by
      convert (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk) using 1
      norm_num
    have hmul := mul_le_mul_of_nonneg_right hfour (show (0 : ℝ) ≤ (n : ℝ) ^ k by positivity)
    rw [mul_pow] at hp
    linarith
  have hs := Finset.sum_le_sum heach
  have hc : (auxiliaryPair j).card = 2 := by simp [auxiliaryPair]
  simp only [Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_ofNat] at hs
  linarith

end Erdos345
