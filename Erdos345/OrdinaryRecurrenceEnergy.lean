import Erdos345.PolynomialFrequencyEnergy

namespace Erdos345

open Finset Polynomial

noncomputable def ordinaryComponentPolynomial {m : ℕ} (a : Fin m → ℂ) : ℂ[X] :=
  ∑ j : Fin m, monomial (j : ℕ) (a j)

theorem ordinaryComponentPolynomial_degree {m : ℕ} (a : Fin m → ℂ) :
    (ordinaryComponentPolynomial a).degree < m := by
  apply mem_degreeLT.mp
  exact (degreeLT ℂ m).sum_mem (fun j _ => monomial_coe_mem_degreeLT j (a j))

theorem ordinaryComponentPolynomial_coeff {m : ℕ} (a : Fin m → ℂ) (j : Fin m) :
    (ordinaryComponentPolynomial a).coeff j = a j := by
  rw [ordinaryComponentPolynomial, finsetSum_coeff, sum_eq_single j]
  · simp
  · intro i _ hij
    rw [coeff_monomial, ite_eq_right (fun h => hij (Fin.ext h))]
  · intro h
    exact False.elim (h (mem_univ _))

theorem ordinaryComponentPolynomial_eval {m : ℕ} (a : Fin m → ℂ) (x : ℂ) :
    (ordinaryComponentPolynomial a).eval x = ∑ j, a j * x ^ (j : ℕ) := by
  simp only [ordinaryComponentPolynomial, eval_finsetSum, eval_monomial]

theorem ordinary_expansion_as_frequency_sum {I : Type*} [Fintype I]
    (m : I → ℕ) (z : I → ℂ) (c : (Σ i, Fin (m i)) → ℂ) (f : ℕ → ℂ)
    (hrep : f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2) (n : ℕ) :
    f n = polynomialFrequencySum
      (fun i => ordinaryComponentPolynomial (fun j => c ⟨i, j⟩)) z n := by
  have h := congrFun hrep n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sigma,
    exponentialPower, exponentialSequence] at h
  rw [h]
  unfold polynomialFrequencySum
  apply sum_congr rfl
  intro i _
  rw [ordinaryComponentPolynomial_eval, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- A long-interval energy bound for the actual ordinary-power expansion
of a cyclotomic recurrence. The top ordinary coefficient is unchanged in
the theorem statement; the Chebyshev conversion has been discharged. -/
theorem ordinary_cyclotomic_expansion_energy_lower
    (N D L : ℕ) (hN : 0 < N) (hD : 0 < D) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (D : ℝ) ^ 4 ≤ Real.pi * L)
    (m : ℕ → ℕ) (hmD : ∀ t ∈ Icc 1 N, m t ≤ D)
    (f : ℕ → ℂ)
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : f = ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (i : CyclotomicRootIndex (Icc 1 N)) (hmi : 0 < m i.1) :
    (L : ℝ) * (Real.pi / (64 * (D : ℝ))) *
        (‖c ⟨i, ⟨m i.1 - 1, by change m i.1 - 1 < m i.1; omega⟩⟩‖ * (L : ℝ) ^ (m i.1 - 1) /
          (4 : ℝ) ^ (m i.1 - 1)) ^ 2 ≤
      ∑ n ∈ range L, ‖f n‖ ^ 2 := by
  let P : CyclotomicRootIndex (Icc 1 N) → ℂ[X] :=
    fun j => ordinaryComponentPolynomial (fun k => c ⟨j, k⟩)
  have h := polynomialFrequency_energy_lower N D L hN hD hL hlarge
    (cyclotomicRootMultiplicity m) (fun j => hmD j.1 j.1.property) P
    (fun j => ordinaryComponentPolynomial_degree (fun k => c ⟨j, k⟩)) i hmi
  have htop : (P i).coeff (m i.1 - 1) =
      c ⟨i, ⟨m i.1 - 1, by change m i.1 - 1 < m i.1; omega⟩⟩ :=
    ordinaryComponentPolynomial_coeff (fun k => c ⟨i, k⟩)
      ⟨m i.1 - 1, by change m i.1 - 1 < m i.1; omega⟩
  simp only [cyclotomicRootMultiplicity] at h
  rw [htop] at h
  have hf (n : ℕ) : f n = polynomialFrequencySum P (@cyclotomicRootValue (Icc 1 N)) n :=
    ordinary_expansion_as_frequency_sum (cyclotomicRootMultiplicity m)
      (@cyclotomicRootValue (Icc 1 N)) c f hrep n
  simp_rw [← hf] at h
  exact h

end Erdos345
