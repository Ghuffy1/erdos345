import Erdos345.FourierParameters
import Erdos345.ReserveRootBound

namespace Erdos345

def reserveCount (N k : ℕ) : ℕ := 512 * (N / (512 * k))

def reservedBases (N k : ℕ) : Finset ℕ := Finset.Icc (N - reserveCount N k + 1) N

theorem reserveCount_le_div (N k : ℕ) : reserveCount N k ≤ N / k := by
  unfold reserveCount
  rw [Nat.mul_comm 512 k, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem reserveCount_le (N k : ℕ) : reserveCount N k ≤ N :=
  (reserveCount_le_div N k).trans (Nat.div_le_self N k)

theorem reserveCount_pos (N k : ℕ) (hk : 0 < k) (hN : 512 * k ≤ N) : 0 < reserveCount N k := by
  have hd : 1 ≤ N / (512 * k) := (Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using hN)
  unfold reserveCount
  omega

theorem reservedBases_card (N k : ℕ) : (reservedBases N k).card = reserveCount N k := by
  have h := reserveCount_le N k
  rw [reservedBases, Nat.card_Icc]
  omega

theorem reservedBases_nonempty (N k : ℕ) (hk : 0 < k) (hN : 512 * k ≤ N) :
    (reservedBases N k).Nonempty := by
  rw [← Finset.card_pos, reservedBases_card]
  exact reserveCount_pos N k hk hN

theorem reservedBases_positive (N k c : ℕ) (hc : c ∈ reservedBases N k) : 0 < c ∧ c ≤ N := by
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hc
  exact ⟨by omega, hu⟩

theorem reservedBases_above_unreserved (N k c : ℕ) (hc : c ∈ reservedBases N k) :
    unreservedEndpoint N k < c := by
  have hS := reserveCount_le_div N k
  have hl := (Finset.mem_Icc.mp hc).1
  unfold unreservedEndpoint
  omega

theorem reservedBases_disjoint (N k : ℕ) :
    Disjoint (reservedBases N k) (unreservedPopulation N k) := by
  apply Finset.disjoint_left.mpr
  intro c hc hr
  have hl := reservedBases_above_unreserved N k c hc
  have hu := ((mem_unreservedPopulation N k c).mp hr).1
  omega

theorem reserveCount_lower (N k : ℕ) (hk : 0 < k) (hN : 2048 * k ≤ N) :
    3 * (N : ℝ) / (4 * (k : ℝ)) ≤ reserveCount N k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrem := Nat.mod_lt N (show 0 < 512 * k by positivity)
  have heq := Nat.mod_add_div N (512 * k)
  have heqR : (N : ℝ) = ((N % (512 * k) : ℕ) : ℝ) + (reserveCount N k : ℝ) * k := by
    rw [reserveCount, Nat.cast_mul]
    have h := congrArg (fun a : ℕ => (a : ℝ)) heq
    push_cast at h
    nlinarith only [h]
  have hremR : ((N % (512 * k) : ℕ) : ℝ) < 512 * (k : ℝ) := by exact_mod_cast hrem
  have hNR : 2048 * (k : ℝ) ≤ N := by exact_mod_cast hN
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem reserved_power_lower (N k c : ℕ) (hk : 20 ≤ k) (hc : c ∈ reservedBases N k) :
    (N : ℝ) ^ k / 4 ≤ (c : ℝ) ^ k := by
  have hroot := quarter_root_endpoint_le N k hk
  have hcU : (unreservedEndpoint N k : ℝ) ≤ c := by
    exact_mod_cast (reservedBases_above_unreserved N k c hc).le
  have hpow := pow_le_pow_left₀
    (show 0 ≤ (N : ℝ) * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) by positivity) (hroot.trans hcU) k
  rw [mul_pow, Real.rpow_inv_natCast_pow (by norm_num) (show k ≠ 0 by omega)] at hpow
  simpa only [div_eq_mul_inv, one_div, one_mul] using hpow

end Erdos345
