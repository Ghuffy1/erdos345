import Erdos345.FourierParameters

namespace Erdos345

theorem unreservedPopulation_card_le (N k : ℕ) : (unreservedPopulation N k).card ≤ N := by
  have hs : unreservedPopulation N k ⊆ Finset.Icc 1 N := by
    intro n hn
    have h := (mem_unreservedPopulation N k n).mp hn
    apply Finset.mem_Icc.mpr
    constructor
    · rcases h.2 with h | h <;> omega
    · exact h.1.trans (Nat.sub_le _ _)
  simpa using Finset.card_le_card hs

theorem unreservedPopulation_nonempty_of_large (N k : ℕ) (hk : 20 ≤ k)
    (hN : 32 * (k : ℝ) ≤ N) : (unreservedPopulation N k).Nonempty := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hU := unreservedEndpoint_ge_three_quarters N k (by omega)
  apply unreservedPopulation_nonempty
  have h : (1 : ℝ) ≤ unreservedEndpoint N k := by linarith
  exact_mod_cast h

theorem sample_floor_lower (N : ℕ) (hN : 16384 ≤ N) :
    (N : ℝ) ≤ 16384 * ((N / 8192 : ℕ) : ℝ) := by
  have heq := Nat.mod_add_div N 8192
  have hm := Nat.mod_lt N (by decide : 0 < 8192)
  have h : N ≤ 16384 * (N / 8192) := by omega
  exact_mod_cast h

theorem sampling_fraction_lower (N k : ℕ) (hR : (unreservedPopulation N k).Nonempty)
    (hN : 16384 ≤ N) :
    (1 : ℝ) / 16384 ≤ ((N / 8192 : ℕ) : ℝ) / (unreservedPopulation N k).card := by
  have hM : (0 : ℝ) < (unreservedPopulation N k).card := by
    exact_mod_cast Finset.card_pos.mpr hR
  have hc : ((unreservedPopulation N k).card : ℝ) ≤ N := by
    exact_mod_cast unreservedPopulation_card_le N k
  have hs := sample_floor_lower N hN
  apply (le_div_iff₀ hM).mpr
  nlinarith

theorem log_fourierN_le (k : ℕ) : Real.log (fourierN k : ℝ) ≤ logScale k ^ 8 + 2 := by
  have hNpos : (0 : ℝ) < fourierN k := by exact_mod_cast fourierN_pos k
  exact (Real.log_le_log hNpos (by linarith : (fourierN k : ℝ) ≤ (fourierN k : ℝ) + 1)).trans
    (log_fourierN_add_one_le k)

theorem fourier_collision_margin (k c : ℕ) (hk : 20 ≤ k) (hc : 0 < c)
    (hcN : c ≤ fourierN k) (hN : 16384 ≤ fourierN k)
    (hNk : 32 * (k : ℝ) ≤ fourierN k) :
    Real.log ((c ^ k : ℕ) : ℝ) - (fourierT k : ℝ) * (fourierH k - 257) /
      (unreservedPopulation (fourierN k) k).card ≤ -(k : ℝ) * logScale k ^ 8 := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hR := unreservedPopulation_nonempty_of_large (fourierN k) k hk hNk
  have hratio := sampling_fraction_lower (fourierN k) k hR hN
  have hH : 0 ≤ fourierH k - 257 := by
    have h : 0 ≤ 65536 * (k : ℝ) * logScale k ^ 8 := by positivity
    unfold fourierH
    linarith
  have he := mul_le_mul_of_nonneg_right hratio hH
  change (1 : ℝ) / 16384 * (fourierH k - 257) ≤
    (fourierT k : ℝ) / (unreservedPopulation (fourierN k) k).card * (fourierH k - 257) at he
  have he' : 4 * (k : ℝ) * logScale k ^ 8 ≤
      (fourierT k : ℝ) * (fourierH k - 257) / (unreservedPopulation (fourierN k) k).card := by
    have hrearrange : (fourierT k : ℝ) / (unreservedPopulation (fourierN k) k).card *
        (fourierH k - 257) = (fourierT k : ℝ) * (fourierH k - 257) /
        (unreservedPopulation (fourierN k) k).card := by ring
    rw [hrearrange] at he
    unfold fourierH at he ⊢
    nlinarith only [he]
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hclog : Real.log (c : ℝ) ≤ logScale k ^ 8 + 2 :=
    (Real.log_le_log hcR (by exact_mod_cast hcN)).trans (log_fourierN_le k)
  have hlogq : Real.log ((c ^ k : ℕ) : ℝ) ≤ (k : ℝ) * (logScale k ^ 8 + 2) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hclog hkR
  have hK8 : 1 ≤ logScale k ^ 8 := one_le_pow₀ (logScale_ge_one k hk0)
  have hKk := mul_le_mul_of_nonneg_left hK8 hkR
  nlinarith only [he', hlogq, hKk]

end Erdos345
