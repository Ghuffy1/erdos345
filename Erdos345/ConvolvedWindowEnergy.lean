import Erdos345.InverseErrorPolynomial

namespace Erdos345

open Finset Polynomial

theorem shiftAction_window_energy_le (p : ℤ[X]) (f : ℕ → ℝ) (a L T : ℕ)
    (hLT : L + p.natDegree ≤ T) (E : ℝ)
    (hE : (∑ j ∈ range T, f (a + j) ^ 2) ≤ E) :
    (∑ j ∈ range L, (shiftAction (p.map (Int.castRingHom ℝ)) f (a + j)) ^ 2) ≤
      coefficientL1 p ^ 2 * E := by
  have heval (j : ℕ) : shiftAction (p.map (Int.castRingHom ℝ)) f (a + j) =
      ∑ i ∈ range (p.natDegree + 1), (p.coeff i : ℝ) * f (a + (j + i)) := by
    rw [shiftAction_sum_of_degree_lt _ _ (natDegree_map_le.trans_lt (Nat.lt_succ_self _))]
    simp only [coeff_map, Int.coe_castRingHom, Nat.add_assoc]
  have h := convolution_energy_le (fun i => (p.coeff i : ℝ)) (fun j => f (a + j)) p.natDegree L T hLT
  calc
    _ = ∑ j ∈ range L, (∑ i ∈ range (p.natDegree + 1), (p.coeff i : ℝ) * f (a + (j + i))) ^ 2 := by
      simp only [heval]
    _ ≤ coefficientL1 p ^ 2 * ∑ j ∈ range T, f (a + j) ^ 2 := h
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- Quantitative recovery of the leading phase from an actual flat
recurrence, using the polynomial Chebyshev energy bound. -/
theorem inverse_energy_from_flat_recurrence (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ)
    (k : ℕ) (hmass : weightMass N w = k + 1)
    (hg : shiftAction (flatPolynomial N w) g = 0) (α : ℝ) (a L T : ℕ)
    (hLT : L + (flatQuotient N w).natDegree ≤ T) (hL : 0 < L)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range T, (α * ((a + j : ℕ) : ℝ) ^ k - (g (a + j) : ℝ)) ^ 2) ≤ E) :
    ∃ u : ℤ, (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)| *
        (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤ E := by
  obtain ⟨u, P, hP, htop, heval⟩ := exists_inverse_error_polynomial N w g k hmass hg α
  let R := taylor (a : ℝ) P
  have hR : R.natDegree ≤ k := by simpa only [R, natDegree_taylor] using hP
  have hRtop : R.coeff k = P.coeff k := taylor_coeff_of_natDegree_le P (a : ℝ) k hP
  have hRval (j : ℕ) : R.eval (j : ℝ) =
      shiftAction ((flatQuotient N w).map (Int.castRingHom ℝ))
        (fun n : ℕ => α * (n : ℝ) ^ k - (g n : ℝ)) (a + j) := by
    have h := heval (a + j)
    simpa only [R, taylor_apply, eval_comp, eval_add, eval_X, eval_C, Nat.cast_add, add_comm] using h
  have hconv := shiftAction_window_energy_le (flatQuotient N w)
    (fun n : ℕ => α * (n : ℝ) ^ k - (g n : ℝ)) a L T hLT E hE
  have henergy : (∑ j ∈ range L, R.eval (j : ℝ) ^ 2) ≤
      (normalizedMoment N w : ℝ) ^ 2 * E := by
    simpa only [hRval, coefficientL1_flatQuotient] using hconv
  have hlow := (real_polynomial_sample_energy_lower R k L hR hL hlarge).trans henergy
  rw [hRtop, htop, abs_mul] at hlow
  have hMpos : (0 : ℝ) < normalizedMoment N w := by exact_mod_cast normalizedMoment_pos N w
  rw [abs_of_pos hMpos] at hlow
  have heq : (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      ((normalizedMoment N w : ℝ) * |α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)| *
        (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 =
      (normalizedMoment N w : ℝ) ^ 2 * ((L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)| *
        (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2) := by ring
  rw [heq] at hlow
  exact ⟨u, (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hMpos)).mp hlow⟩

end Erdos345
