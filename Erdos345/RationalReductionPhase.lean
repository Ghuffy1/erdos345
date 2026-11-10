import Erdos345.WindowConductorReduction

namespace Erdos345

open Finset Polynomial

/-- An exact modular reduction gives a rational polynomial phase with the
same denominator and numerator residue at every integer input. -/
theorem exists_rational_reduction_phase (q u k d : ℕ) (hq : 0 < q)
    (hred : q ∣ reductionModulus k d) :
    ∃ P : ℚ[X], P.natDegree ≤ d ∧ integerValuedPolynomial (C (q : ℚ) * P) ∧
      ∀ n : ℤ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
        (q : ℤ) ∣ A - (u : ℤ) * n ^ k := by
  obtain ⟨R, hdegree, hInt, hmod⟩ :=
    (hasGlobalIntegerPolynomialReduction_iff_dvd q k d).mpr hred
  let P : ℚ[X] := C ((u : ℚ) / q) * R
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hpoly : C (q : ℚ) * P = C (u : ℚ) * R := by
    dsimp only [P]
    rw [← mul_assoc, ← C_mul]
    congr 2
    field_simp
  have heval (n : ℤ) : (q : ℚ) * P.eval (n : ℚ) = (u : ℚ) * R.eval (n : ℚ) := by
    have h := congrArg (fun A : ℚ[X] => A.eval (n : ℚ)) hpoly
    simpa only [eval_mul, eval_C] using h
  refine ⟨P, ?_, ?_, ?_⟩
  · exact (natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using hdegree))
  · rw [hpoly]
    intro n
    obtain ⟨z, hz⟩ := hInt n
    refine ⟨(u : ℤ) * z, ?_⟩
    simp only [eval_mul, eval_C, hz, Int.cast_mul, Int.cast_natCast]
  · intro n
    obtain ⟨z, hz, hdiv⟩ := hmod n
    refine ⟨(u : ℤ) * z, ?_, ?_⟩
    · simpa only [hz, Int.cast_mul, Int.cast_natCast] using heval n
    · have h := dvd_neg.mpr (dvd_mul_of_dvd_right hdiv (u : ℤ))
      convert h using 1
      ring

theorem rational_phase_int_shift (P : ℚ[X]) (q u k n : ℕ) (hq : 0 < q)
    (hmod : ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k) :
    ∃ z : ℤ, P.eval (n : ℚ) = (u : ℚ) / q * (n : ℚ) ^ k + (z : ℚ) := by
  obtain ⟨A, hA, z, hz⟩ := hmod
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hzQ : (A : ℚ) - (u : ℚ) * (n : ℚ) ^ k = (q : ℚ) * z := by exact_mod_cast hz
  refine ⟨z, ?_⟩
  apply (mul_left_cancel₀ hqQ)
  rw [hA]
  field_simp
  nlinarith

theorem sin_pi_sq_int_shift (x : ℝ) (z : ℤ) :
    Real.sin (Real.pi * (x + z)) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
  rw [show Real.pi * (x + z) = Real.pi * x + (z : ℝ) * Real.pi by ring,
    Real.sin_add_int_mul_pi, mul_pow]
  have hsign : ((-1 : ℝ) ^ z) ^ 2 = 1 := by
    change (((-1 : ℝ) ^ z) ^ (2 : ℤ)) = 1
    rw [← zpow_mul, Int.mul_comm z 2, zpow_mul]
    norm_num
  rw [hsign, one_mul]

/-- The exact polynomial reduction preserves the ORIGINAL phase energy;
no Chinese-remainder projection or change of denominator occurs. -/
theorem rational_phase_sineEnergy_eq_center (P : ℚ[X]) (q u k X : ℕ) (hq : 0 < q)
    (hmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k) :
    sineEnergy (fun n : ℕ => ((P.eval (n : ℚ) : ℚ) : ℝ)) X = centerEnergy k u q X := by
  unfold sineEnergy centerEnergy
  apply sum_congr rfl
  intro n _
  obtain ⟨z, hz⟩ := rational_phase_int_shift P q u k n hq (hmod n)
  have hzR : ((P.eval (n : ℚ) : ℚ) : ℝ) = (u : ℝ) / q * (n : ℝ) ^ k + (z : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_intCast] using congrArg (fun x : ℚ => (x : ℝ)) hz
  change Real.sin (Real.pi * ((P.eval (n : ℚ) : ℚ) : ℝ)) ^ 2 = _
  rw [hzR, sin_pi_sq_int_shift]
  unfold centerTerm
  congr 2
  ring

end Erdos345
