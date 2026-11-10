import Erdos345.PrimeThetaLower
import Erdos345.BelovBoundedPositivity

namespace Erdos345

theorem odd_prime_mass_lower (N : ℕ) (hN : 16384 ≤ N) :
    (N : ℝ) ^ 2 / (25 * Real.log N) ≤ ∑ p ∈ (Nat.primesLE N).erase 2, (p : ℝ) := by
  classical
  let P := Nat.primesLE N
  let S := P.filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ) / 8)
  let L := P.filter (fun p : ℕ => ¬(p : ℝ) ≤ (N : ℝ) / 8)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hsmall : (∑ p ∈ S, Real.log (p : ℝ)) ≤ Chebyshev.theta ((N : ℝ) / 8) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hp
      apply Nat.mem_primesLE.mpr
      exact ⟨Nat.le_floor hle, (Nat.mem_primesLE.mp hp).2⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have hlarge_subset : L ⊆ P.erase 2 := by
    intro p hp
    obtain ⟨hp, hgt⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_erase.mpr
    refine ⟨?_, hp⟩
    intro heq
    subst p
    have hNr : (16384 : ℝ) ≤ N := by exact_mod_cast hN
    norm_num at hgt
    linarith
  have hlarge : (∑ p ∈ L, Real.log (p : ℝ)) ≤
      (8 * Real.log N / N) * (∑ p ∈ P.erase 2, (p : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ L, (8 * Real.log N / N) * (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp, hgt⟩ := Finset.mem_filter.mp hp
        have hpdata := Nat.mem_primesLE.mp hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpdata.2.pos
        have hpN : (p : ℝ) ≤ N := by exact_mod_cast hpdata.1
        have hplog := Real.log_le_log hp0 hpN
        have hweight : Real.log (N : ℝ) ≤ (8 * Real.log N / N) * (p : ℝ) := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hN0).mpr
          have hm := mul_le_mul_of_nonneg_right (show (N : ℝ) ≤ 8 * p by linarith) hlog.le
          nlinarith
        exact hplog.trans hweight
      _ = (8 * Real.log N / N) * (∑ p ∈ L, (p : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hlarge_subset (fun p _ _ => Nat.cast_nonneg p))
        (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p : ℕ => (p : ℝ) ≤ (N : ℝ) / 8) (fun p => Real.log (p : ℝ))
  have htheta : Chebyshev.theta N ≤ Chebyshev.theta ((N : ℝ) / 8) +
      (8 * Real.log N / N) * (∑ p ∈ P.erase 2, (p : ℝ)) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    dsimp only [S, L] at hsmall hlarge
    linarith
  have hupper := Chebyshev.theta_le_log4_mul_x (show 0 ≤ (N : ℝ) / 8 by positivity)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hupper
  have htwo : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_right htwo (show 0 ≤ (N : ℝ) / 4 by positivity)
  have hlower := prime_theta_half_large N hN
  have hmass : (13 / 40 : ℝ) * N ≤ (8 * Real.log N / N) * (∑ p ∈ P.erase 2, (p : ℝ)) := by
    nlinarith
  simp only [div_mul_eq_mul_div] at hmass
  have hmass' := (le_div_iff₀ hN0).mp hmass
  apply (div_le_iff₀ (show 0 < 25 * Real.log (N : ℝ) by positivity)).mpr
  change (N : ℝ) ^ 2 ≤ (∑ p ∈ P.erase 2, (p : ℝ)) * (25 * Real.log N)
  nlinarith [sq_nonneg (N : ℝ)]

theorem belov_prime_mass_lower (q j : ℕ) (hN : 16384 ≤ q * (j + 1) ^ 2) :
    ((q * (j + 1) ^ 2 : ℕ) : ℝ) ^ 2 / (25 * Real.log ((q * (j + 1) ^ 2 : ℕ) : ℝ)) ≤
      ∑ p ∈ belovLevelPrimes q j, (p : ℝ) :=
  odd_prime_mass_lower _ hN

end Erdos345
