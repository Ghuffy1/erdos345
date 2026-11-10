import Erdos345.PrimeSineBinBounds

namespace Erdos345

theorem sum_abs_prime_sine_harmonic (P : Finset ℕ) (A v : ℕ) (t : ℝ)
    (hA : 2 ≤ A) (ht : 1 < t) (hprime : ∀ p ∈ P, p.Prime)
    (hbound : ∀ p ∈ P, p ≤ A) (hsmall : ∀ p ∈ P, (p : ℝ) < t / 2) :
    (∑ p ∈ P, |scaledSineBlock p v t|) ≤
      (4 * (A : ℝ) * Real.log t / Real.log (A : ℝ)) *
        ((v : ℝ) + (harmonic A : ℝ) / 2) := by
  classical
  let P0 := P.filter (fun p => primePhaseBin (t / 2) p = 0)
  let P1 := P.filter (fun p => primePhaseBin (t / 2) p ≠ 0)
  let K : ℝ := 4 * (A : ℝ) * Real.log t / Real.log (A : ℝ)
  have hzero : (∑ p ∈ P0, |scaledSineBlock p v t|) ≤ K * v := by
    apply sum_abs_sine_zero_bin P0 A v t hA ht
    · intro p hp; exact hprime p (Finset.mem_filter.mp hp).1
    · intro p hp; exact hbound p (Finset.mem_filter.mp hp).1
    · intro p hp; exact hsmall p (Finset.mem_filter.mp hp).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
  have hmap : ∀ p ∈ P1, primePhaseBin (t / 2) p ∈ Finset.Icc 1 A := by
    intro p hp
    obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
    have hb := (primePhaseBin_le_distance (t / 2) p).trans
      (primePhaseDistance_le_half (t / 2) p (hprime p hpP).pos)
    have hpa : (p : ℝ) ≤ A := by exact_mod_cast hbound p hpP
    have hlast : (primePhaseBin (t / 2) p : ℝ) ≤ A := by nlinarith
    exact Finset.mem_Icc.mpr ⟨by omega, by exact_mod_cast hlast⟩
  have hf : ∀ j ∈ Finset.Icc 1 A,
      (∑ p ∈ P1.filter (fun p => primePhaseBin (t / 2) p = j), |scaledSineBlock p v t|) ≤
        K / (2 * (j : ℝ)) := by
    intro j hj
    apply sum_abs_sine_positive_bin _ A v j t hA (Finset.mem_Icc.mp hj).1 ht
    · intro p hp; exact hprime p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp; exact hbound p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp; exact hsmall p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
  have hpos : (∑ p ∈ P1, |scaledSineBlock p v t|) ≤ K / 2 * (harmonic A : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 A,
          ∑ p ∈ P1.filter (fun p => primePhaseBin (t / 2) p = j), |scaledSineBlock p v t| :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
      _ ≤ ∑ j ∈ Finset.Icc 1 A, K / (2 * (j : ℝ)) := Finset.sum_le_sum hf
      _ = K / 2 * (harmonic A : ℝ) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, mul_inv_rev]
        ring
  have hsplit : (∑ p ∈ P, |scaledSineBlock p v t|) =
      (∑ p ∈ P0, |scaledSineBlock p v t|) + (∑ p ∈ P1, |scaledSineBlock p v t|) := by
    exact (Finset.sum_filter_add_sum_filter_not P (fun p => primePhaseBin (t / 2) p = 0) _).symm
  rw [hsplit]
  change _ ≤ K * ((v : ℝ) + (harmonic A : ℝ) / 2)
  nlinarith

theorem sum_abs_prime_sine_bound (P : Finset ℕ) (A v : ℕ) (t : ℝ)
    (hA : 4 ≤ A) (ht : 1 < t) (hprime : ∀ p ∈ P, p.Prime)
    (hbound : ∀ p ∈ P, p ≤ A) (hsmall : ∀ p ∈ P, (p : ℝ) < t / 2) :
    (∑ p ∈ P, |scaledSineBlock p v t|) ≤
      4 * (A : ℝ) * (1 + (v : ℝ) / Real.log (A : ℝ)) * Real.log t := by
  have hlogA : 1 ≤ Real.log (A : ℝ) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ A by exact_mod_cast hA)
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq] at hl
    linarith [log_two_profile_bounds.1]
  have hK : 0 ≤ 4 * (A : ℝ) * Real.log t / Real.log (A : ℝ) := by
    have htlog : 0 < Real.log t := Real.log_pos ht
    positivity
  have hharm : (harmonic A : ℝ) / 2 ≤ Real.log (A : ℝ) := by
    have h := harmonic_le_one_add_log A
    linarith
  have hb := sum_abs_prime_sine_harmonic P A v t (by omega) ht hprime hbound hsmall
  have hs := mul_le_mul_of_nonneg_left (add_le_add_right hharm (v : ℝ)) hK
  apply hb.trans
  calc
    _ ≤ (4 * (A : ℝ) * Real.log t / Real.log (A : ℝ)) * ((v : ℝ) + Real.log (A : ℝ)) := by
      simpa only [add_comm] using hs
    _ = _ := by
      have hn : Real.log (A : ℝ) ≠ 0 := by linarith
      field_simp
      ring

end Erdos345
