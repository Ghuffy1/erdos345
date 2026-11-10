import Erdos345.EnergyLogBound

namespace Erdos345

open Finset Polynomial

def padExpansionCoefficient {K I : Type*} [Zero K] {m M : I → ℕ}
    (a : (Σ i, Fin (m i)) → K) (ij : (Σ i, Fin (M i))) : K :=
  padFin (fun j => a ⟨ij.1, j⟩) ij.2

theorem pad_exponential_expansion {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m M : I → ℕ) (hm : ∀ i, m i ≤ M i)
    (a : (Σ i, Fin (m i)) → K) :
    (∑ ij : (Σ i, Fin (M i)), padExpansionCoefficient a ij • exponentialPower (z ij.1) ij.2) =
      ∑ ij : (Σ i, Fin (m i)), a ij • exponentialPower (z ij.1) ij.2 := by
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  exact sum_padFin_smul (fun j => a ⟨i, j⟩) (hm i)
    (fun j => exponentialPower (z i) j)

def polynomialExpansionCoefficient {K I : Type*} [Field K] [DecidableEq I]
    (M : I → ℕ) (i₀ : I) (P : K[X]) (ij : (Σ i, Fin (M i))) : K :=
  if ij.1 = i₀ then P.coeff ij.2 else 0

theorem polynomial_exponential_expansion {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (z : I → K) (M : I → ℕ) (i₀ : I) (hz : z i₀ = 1) (P : K[X]) (hP : P.degree < M i₀) :
    (fun n : ℕ => P.eval (n : K)) =
      ∑ ij : (Σ i, Fin (M i)), polynomialExpansionCoefficient M i₀ P ij •
        exponentialPower (z ij.1) ij.2 := by
  rw [Fintype.sum_sigma, sum_eq_single i₀]
  · funext n
    have h := eval_eq_sum_degreeLTEquiv (mem_degreeLT.mpr hP) (n : K)
    change P.eval (n : K) = ∑ j : Fin (M i₀), P.coeff j * (n : K) ^ (j : ℕ) at h
    simpa only [polynomialExpansionCoefficient, ite_true, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, exponentialPower, exponentialSequence, hz, one_pow, one_mul] using h
  · intro i _ hi
    apply sum_eq_zero
    intro j _
    simp only [polynomialExpansionCoefficient, ite_eq_right hi, zero_smul]
  · intro h
    exact False.elim (h (mem_univ _))

/-- In a common independent expansion, a polynomial perturbation affects
only the unit-root coefficient block. -/
theorem nonunit_expansion_sum_zero {K I : Type*} [Field K] [CharZero K]
    [Fintype I] [DecidableEq I]
    (z : I → K) (M : I → ℕ) (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0)
    (i₀ : I) (hroot : z i₀ = 1) (P : K[X]) (hP : P.degree < M i₀)
    (f g : ℕ → K) (hfP : f + g = fun n : ℕ => P.eval (n : K))
    (a b : (Σ i, Fin (M i)) → K)
    (ha : f = ∑ ij, a ij • exponentialPower (z ij.1) ij.2)
    (hb : g = ∑ ij, b ij • exponentialPower (z ij.1) ij.2) :
    ∀ i, i ≠ i₀ → ∀ j : Fin (M i), a ⟨i, j⟩ + b ⟨i, j⟩ = 0 := by
  have hpoly := polynomial_exponential_expansion z M i₀ hroot P hP
  have hzero : (∑ ij, (a ij + b ij - polynomialExpansionCoefficient M i₀ P ij) •
      exponentialPower (z ij.1) ij.2) = 0 := by
    simp_rw [sub_smul, add_smul, sum_sub_distrib, sum_add_distrib]
    rw [← ha, ← hb, ← hpoly, hfP, sub_self]
  have hli := exponentialPower_family_linearIndependent z M hinj hz
  intro i hi j
  have h := Fintype.linearIndependent_iff.mp hli _ hzero ⟨i, j⟩
  simpa only [polynomialExpansionCoefficient, ite_eq_right hi, sub_zero] using h

theorem multiplicity_le_of_padded_sum_zero {K : Type*} [Field K]
    {m n M : ℕ} (a : Fin m → K) (b : Fin n → K)
    (hm : m ≤ M)
    (ha : ∀ hp : 0 < m, a ⟨m - 1, by omega⟩ ≠ 0)
    (hsum : ∀ j : Fin M, padFin a j + padFin b j = 0) : m ≤ n := by
  by_contra hmn
  have hp : 0 < m := by omega
  let j : Fin M := ⟨m - 1, by omega⟩
  have h := hsum j
  have hjm : m - 1 < m := by omega
  have hjn : ¬m - 1 < n := by omega
  change (if h : m - 1 < m then a ⟨m - 1, h⟩ else 0) +
    (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0) = 0 at h
  rw [dite_eq_left hjm, dite_eq_right hjn, add_zero] at h
  exact ha hp h

theorem multiplicities_eq_of_padded_sum_zero {K : Type*} [Field K]
    {m n M : ℕ} (a : Fin m → K) (b : Fin n → K)
    (hm : m ≤ M) (hn : n ≤ M)
    (ha : ∀ hp : 0 < m, a ⟨m - 1, by omega⟩ ≠ 0)
    (hb : ∀ hp : 0 < n, b ⟨n - 1, by omega⟩ ≠ 0)
    (hsum : ∀ j : Fin M, padFin a j + padFin b j = 0) : m = n := by
  apply Nat.le_antisymm (multiplicity_le_of_padded_sum_zero a b hm ha hsum)
  apply multiplicity_le_of_padded_sum_zero b a hn hb
  intro j
  rw [add_comm]
  exact hsum j

end Erdos345
