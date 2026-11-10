import Erdos345.SineDistanceBound

namespace Erdos345

theorem phase_floor_bounds (y : ℝ) (j : ℕ) (hy : 2 < y) (hj : (j : ℝ) < y / 2) :
    (⌊y⌋ - (j : ℤ) ≠ 0) ∧ (⌊-y⌋ - (j : ℤ) ≠ 0) ∧
      |((⌊y⌋ - (j : ℤ) : ℤ) : ℝ)| ≤ 2 * y ∧
      |((⌊-y⌋ - (j : ℤ) : ℤ) : ℝ)| ≤ 2 * y := by
  have hyl := Int.lt_floor_add_one y
  have hyu := Int.floor_le y
  have hnl := Int.lt_floor_add_one (-y)
  have hnu := Int.floor_le (-y)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ha : 0 < (⌊y⌋ : ℝ) - j := by linarith
  have hb : (⌊-y⌋ : ℝ) - j < 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (0 : ℤ) < ⌊y⌋ - (j : ℤ) := by exact_mod_cast ha
    exact ne_of_gt h
  · have h : ⌊-y⌋ - (j : ℤ) < (0 : ℤ) := by exact_mod_cast hb
    exact ne_of_lt h
  · push_cast
    rw [abs_of_pos ha]
    linarith
  · push_cast
    rw [abs_of_neg hb]
    linarith

theorem sum_prime_logs_of_phaseBin (P : Finset ℕ) (y : ℝ) (j : ℕ)
    (hy : 1 / 2 < y) (hprime : ∀ p ∈ P, p.Prime)
    (hpy : ∀ p ∈ P, (p : ℝ) < y)
    (hbin : ∀ p ∈ P, primePhaseBin y p = j) :
    (∑ p ∈ P, Real.log (p : ℝ)) ≤ 2 * Real.log (2 * y) := by
  classical
  by_cases hne : P.Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hy2 : 2 < y := hp2.trans_lt (hpy p hp)
    have hj : (j : ℝ) < y / 2 := by
      have h := (primePhaseBin_le_distance y p).trans (primePhaseDistance_le_half y p (hprime p hp).pos)
      rw [hbin p hp] at h
      linarith [hpy p hp]
    obtain ⟨ha, hb, hA, hB⟩ := phase_floor_bounds y j hy2 hj
    let A : ℤ := ⌊y⌋ - (j : ℤ)
    let B : ℤ := ⌊-y⌋ - (j : ℤ)
    have hprodne : A * B ≠ 0 := mul_ne_zero ha hb
    have hN : 0 < (A * B).natAbs := Int.natAbs_pos.mpr hprodne
    have hdiv : ∀ r ∈ P, r ∣ (A * B).natAbs := by
      intro r hr
      apply Int.natCast_dvd.mp
      have hd := primePhaseBin_dvd_alternative y r
      rw [hbin r hr] at hd
      exact hd.elim (fun h => dvd_mul_of_dvd_left h B) (fun h => dvd_mul_of_dvd_right h A)
    have hprod : ∏ r ∈ P, r ∣ (A * B).natAbs :=
      Finset.prod_primes_dvd _ (fun r hr => (hprime r hr).prime) hdiv
    have hle : ∏ r ∈ P, r ≤ (A * B).natAbs := Nat.le_of_dvd hN hprod
    have hpos : (0 : ℝ) < (∏ r ∈ P, r : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun r hr => (hprime r hr).pos)
    have hbound : ((A * B).natAbs : ℝ) ≤ (2 * y) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul]
      have hm := mul_le_mul hA hB (abs_nonneg (B : ℝ)) (by linarith : 0 ≤ 2 * y)
      simpa only [pow_two] using hm
    calc
      (∑ r ∈ P, Real.log (r : ℝ)) = Real.log ((∏ r ∈ P, r : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod (fun r hr => by exact_mod_cast (hprime r hr).ne_zero)]
      _ ≤ Real.log ((A * B).natAbs : ℝ) := Real.log_le_log hpos (by exact_mod_cast hle)
      _ ≤ Real.log ((2 * y) ^ 2) := Real.log_le_log (by exact_mod_cast hN) hbound
      _ = 2 * Real.log (2 * y) := by rw [Real.log_pow]; norm_num
  · have he : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp only [Finset.sum_empty]
    have hlog : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
    linarith

end Erdos345
