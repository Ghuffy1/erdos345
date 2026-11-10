import Erdos345.PolynomialShiftAction

namespace Erdos345

open Finset Polynomial

/-- The already checked Chebyshev sampling estimate gives a quantitative
bound for the top coefficient of any polynomial on a long integer interval. -/
theorem polynomial_sample_energy_lower (P : ℂ[X]) (k L : ℕ)
    (hP : P.natDegree ≤ k) (hL : 0 < L)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (‖P.coeff k‖ * (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤
        ∑ n ∈ range L, ‖P.eval (n : ℂ)‖ ^ 2 := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hdeg : P.degree < (k + 1 : ℕ) :=
    degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hP))
  obtain ⟨c, _hc0, hc, hctop⟩ := exists_scaled_chebyshev_expansion P (L : ℂ) hLc
    (k + 1) (k + 1) le_rfl hdeg
  have htop := scaled_chebyshev_top_norm_lower P (L : ℂ) k (c ⟨k, by omega⟩)
    (by simpa only [Nat.add_sub_cancel] using hctop (Nat.succ_pos k))
  rw [Complex.norm_natCast] at htop
  have hsq := pow_le_pow_left₀
    (show 0 ≤ ‖P.coeff k‖ * (L : ℝ) ^ k / (4 : ℝ) ^ k by positivity) htop 2
  have hsingle : ‖c ⟨k, by omega⟩‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 :=
    single_le_sum (fun j _ => sq_nonneg ‖c j‖) (mem_univ _)
  have he := shiftedChebyshevSeries_sampled_half_energy_lower (Nat.succ_pos k) c L hL hlarge
  have hscale : 0 ≤ (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) := by positivity
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    _ ≤ (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) * (∑ j, ‖c j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsq.trans hsingle) hscale
    _ ≤ (L : ℝ) * ((1 / (L : ℝ)) *
        ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left he hLR.le
      simpa only [mul_assoc] using h
    _ = ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2 := by
      field_simp
    _ = _ := by
      apply sum_congr rfl
      intro n _
      rw [scaled_chebyshev_samples P c L hL hc n]

theorem real_polynomial_sample_energy_lower (P : ℝ[X]) (k L : ℕ)
    (hP : P.natDegree ≤ k) (hL : 0 < L)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|P.coeff k| * (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤
        ∑ n ∈ range L, (P.eval (n : ℝ)) ^ 2 := by
  have h := polynomial_sample_energy_lower (P.map (algebraMap ℝ ℂ)) k L
    (natDegree_map_le.trans hP) hL hlarge
  have heval (n : ℕ) : (P.map (algebraMap ℝ ℂ)).eval (n : ℂ) = (algebraMap ℝ ℂ) (P.eval (n : ℝ)) := by
    simpa only [map_natCast] using
      (eval_map_apply (f := algebraMap ℝ ℂ) (p := P) (n : ℝ))
  simp only [heval, coeff_map, norm_algebraMap', Real.norm_eq_abs, sq_abs] at h
  exact h

end Erdos345
