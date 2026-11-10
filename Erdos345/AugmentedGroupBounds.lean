import Erdos345.FinitePowerSums
import Erdos345.ReservedAllocation

namespace Erdos345

theorem reserved_augmentation_card_lower (N k : ℕ) (G B : Finset ℕ)
    (hk : 20 ≤ k) (hB : B ⊆ reservedBases N k) (hdisj : Disjoint G B)
    (hgood : ∀ b ∈ B,
      ((b ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues G k (b ^ k)).card) :
    (B.card : ℝ) * (N : ℝ) ^ k / 16 ≤ (finitePowerSums (G ∪ B) k).card := by
  have hgrowth := finitePowerSums_union_growth G B k hdisj
    (fun b hb => (reservedBases_positive N k b (hB hb)).1)
  have hR : ((finitePowerSums G k).card : ℝ) +
      (∑ b ∈ B, ((representedResidues G k (b ^ k)).card : ℝ)) ≤
      (finitePowerSums (G ∪ B) k).card := by exact_mod_cast hgrowth
  have heach (b : ℕ) (hb : b ∈ B) :
      (N : ℝ) ^ k / 16 ≤ (representedResidues G k (b ^ k)).card := by
    have hp := reserved_power_lower N k b hk (hB hb)
    have hs := hgood b hb
    simp only [Nat.cast_pow] at hs
    linarith
  have hsum := Finset.sum_le_sum heach
  have hsum' : (B.card : ℝ) * (N : ℝ) ^ k / 16 ≤
      ∑ b ∈ B, ((representedResidues G k (b ^ k)).card : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc] using hsum
  have hz : (0 : ℝ) ≤ (finitePowerSums G k).card := Nat.cast_nonneg _
  linarith

theorem reserveGroupSize_lower (N k : ℕ) (hk : 0 < k) (hN : 2048 * k ≤ N) :
    3 * (N : ℝ) / (2048 * (k : ℝ)) ≤ reserveGroupSize N k := by
  have h := reserveCount_lower N k hk hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have heq : (reserveCount N k : ℝ) = 512 * (reserveGroupSize N k : ℝ) := by
    simp only [reserveCount, reserveGroupSize, Nat.cast_mul, Nat.cast_ofNat]
  rw [heq] at h
  apply (div_le_iff₀ (by positivity)).mpr
  have h' := (div_le_iff₀ (show (0 : ℝ) < 4 * k by positivity)).mp h
  nlinarith

theorem selected_span_le_reserve_third (N k : ℕ) (hk : 0 < k)
    (hN : 2048 * k ≤ N) :
    4 * ((N : ℝ) ^ (k + 1) / ((8192 : ℝ) * k)) ≤
      (reserveGroupSize N k : ℝ) * (N : ℝ) ^ k / 3 := by
  have hs := reserveGroupSize_lower N k hk hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ (N : ℝ) ^ k by positivity)
  rw [pow_succ]
  calc
    4 * ((N : ℝ) ^ k * N / ((8192 : ℝ) * k)) =
        (3 * (N : ℝ) / (2048 * k) * (N : ℝ) ^ k) / 3 := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hmul (by norm_num)

theorem reserved_augmentation_span_upper (N k : ℕ) (G B : Finset ℕ)
    (hk : 0 < k) (hN : 2048 * k ≤ N) (hdisj : Disjoint G B)
    (hB : B ⊆ reservedBases N k) (hcard : B.card = reserveGroupSize N k)
    (hspan : (∑ n ∈ G, (n : ℝ) ^ k) <
      4 * ((N : ℝ) ^ (k + 1) / ((8192 : ℝ) * k))) :
    (∑ n ∈ G ∪ B, (n : ℝ) ^ k) <
      (4 : ℝ) / 3 * (reserveGroupSize N k : ℝ) * (N : ℝ) ^ k := by
  have hG := hspan.trans_le (selected_span_le_reserve_third N k hk hN)
  have hBsum : (∑ n ∈ B, (n : ℝ) ^ k) ≤
      (reserveGroupSize N k : ℝ) * (N : ℝ) ^ k := by
    calc
      (∑ n ∈ B, (n : ℝ) ^ k) ≤ ∑ _n ∈ B, (N : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (Nat.cast_nonneg n)
          (by exact_mod_cast (reservedBases_positive N k n (hB hn)).2) k
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [Finset.sum_union hdisj]
  linarith

end Erdos345
