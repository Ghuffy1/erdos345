import Erdos345.ScaledChebyshevBasis

namespace Erdos345

open Finset Polynomial

noncomputable def polynomialFrequencySum {I : Type*} [Fintype I]
    (P : I → ℂ[X]) (z : I → ℂ) (n : ℕ) : ℂ :=
  ∑ i, z i ^ n * (P i).eval (n : ℂ)

theorem scaled_chebyshev_samples {D : ℕ} (P : ℂ[X]) (d : Fin D → ℂ)
    (L : ℕ) (hL : 0 < L)
    (hd : P.comp (C (L : ℂ) * X) = ∑ j, d j • shiftedChebyshev ℂ j) (n : ℕ) :
    shiftedChebyshevSeries d ((n : ℝ) / L) = P.eval (n : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hx : (L : ℂ) * (((n : ℝ) / L : ℝ) : ℂ) = n := by push_cast; field_simp
  have h := congrArg (fun Q : ℂ[X] => Q.eval (((n : ℝ) / L : ℝ) : ℂ)) hd
  simp only [eval_comp, eval_mul, eval_C, eval_X, hx, eval_finsetSum, eval_smul, smul_eq_mul] at h
  exact h.symm

/-- The proved Chebyshev energy estimate transferred to ordinary
polynomial-exponential components, with the actual top coefficient tracked. -/
theorem polynomialFrequency_energy_lower
    (N D L : ℕ) (hN : 0 < N) (hD : 0 < D) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (D : ℝ) ^ 4 ≤ Real.pi * L)
    (m : CyclotomicRootIndex (Icc 1 N) → ℕ)
    (hmD : ∀ i, m i ≤ D)
    (P : CyclotomicRootIndex (Icc 1 N) → ℂ[X])
    (hP : ∀ i, (P i).degree < m i)
    (i : CyclotomicRootIndex (Icc 1 N)) (hmi : 0 < m i) :
    (L : ℝ) * (Real.pi / (64 * (D : ℝ))) *
        (‖(P i).coeff (m i - 1)‖ * (L : ℝ) ^ (m i - 1) / (4 : ℝ) ^ (m i - 1)) ^ 2 ≤
      ∑ n ∈ range L,
        ‖polynomialFrequencySum P (@cyclotomicRootValue (Icc 1 N)) n‖ ^ 2 := by
  classical
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hex (j : CyclotomicRootIndex (Icc 1 N)) :=
    exists_scaled_chebyshev_expansion (P j) (L : ℂ) hLc (m j) D (hmD j) (hP j)
  choose d hd0 hd hdtop using hex
  have hsample (j : CyclotomicRootIndex (Icc 1 N)) (n : ℕ) :
      chebyshevPhase (cyclotomicRootValue j) (d j) L n =
        cyclotomicRootValue j ^ n * (P j).eval (n : ℂ) := by
    rw [chebyshevPhase, modulatedSequence, scaled_chebyshev_samples (P j) (d j) L hL (hd j), mul_comm]
  have he := cyclotomicChebyshev_energy_lower N D L hN hD hL hlarge d
  have hsum : (∑ n ∈ range L, ‖∑ j, chebyshevPhase (cyclotomicRootValue j) (d j) L n‖ ^ 2) =
      ∑ n ∈ range L, ‖polynomialFrequencySum P (@cyclotomicRootValue (Icc 1 N)) n‖ ^ 2 := by
    apply sum_congr rfl
    intro n _
    simp_rw [hsample]
    rfl
  rw [hsum] at he
  let top : Fin D := ⟨m i - 1, by have := hmD i; omega⟩
  have htop := scaled_chebyshev_top_norm_lower (P i) (L : ℂ) (m i - 1) (d i top) (hdtop i hmi)
  rw [Complex.norm_natCast] at htop
  have hpos : 0 ≤ ‖(P i).coeff (m i - 1)‖ * (L : ℝ) ^ (m i - 1) /
      (4 : ℝ) ^ (m i - 1) := by positivity
  have hsq := pow_le_pow_left₀ hpos htop 2
  have hrow : ‖d i top‖ ^ 2 ≤ ∑ j, ‖d i j‖ ^ 2 :=
    single_le_sum (f := fun j => ‖d i j‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ top)
  have hall : (∑ j, ‖d i j‖ ^ 2) ≤ ∑ j, ∑ k, ‖d j k‖ ^ 2 :=
    single_le_sum (f := fun j => ∑ k, ‖d j k‖ ^ 2)
      (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_univ i)
  have hscale : 0 ≤ (L : ℝ) * (Real.pi / (64 * (D : ℝ))) := by positivity
  exact (mul_le_mul_of_nonneg_left (hsq.trans (hrow.trans hall)) hscale).trans he

end Erdos345
