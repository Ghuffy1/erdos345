import Erdos345.FlatPolynomial
import Erdos345.IntegerValuedPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.LinearMap.End

namespace Erdos345

open Finset Polynomial

noncomputable def sequenceShift (R : Type*) [CommRing R] : Module.End R (ℕ → R) where
  toFun f n := f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def shiftAction {R : Type*} [CommRing R] (p : R[X]) :
    Module.End R (ℕ → R) := aeval (sequenceShift R) p

theorem sequenceShift_pow {R : Type*} [CommRing R] (f : ℕ → R) (h n : ℕ) :
    ((sequenceShift R) ^ h) f n = f (n + h) := by
  induction h generalizing n with
  | zero => rfl
  | succ h ih =>
    rw [pow_succ', Module.End.mul_apply]
    change ((sequenceShift R) ^ h) f (n + 1) = f (n + (h + 1))
    rw [ih]
    congr 1
    omega

theorem shiftAction_mul {R : Type*} [CommRing R] (p q : R[X]) (f : ℕ → R) :
    shiftAction (p * q) f = shiftAction p (shiftAction q f) := by
  simp only [shiftAction, map_mul, Module.End.mul_apply]

theorem shiftAction_add {R : Type*} [CommRing R] (p q : R[X]) (f : ℕ → R) :
    shiftAction (p + q) f = shiftAction p f + shiftAction q f := by
  simp only [shiftAction, map_add, LinearMap.add_apply]

theorem shiftAction_sum {R : Type*} [CommRing R] (p : R[X]) (f : ℕ → R) (n : ℕ) :
    shiftAction p f n = ∑ i ∈ range (p.natDegree + 1), p.coeff i * f (n + i) := by
  rw [shiftAction, aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply,
    Pi.smul_apply, smul_eq_mul, sequenceShift_pow]

theorem shiftAction_sum_of_degree_lt {R : Type*} [CommRing R] (p : R[X])
    (f : ℕ → R) {D : ℕ} (hD : p.natDegree < D) (n : ℕ) :
    shiftAction p f n = ∑ i ∈ range D, p.coeff i * f (n + i) := by
  rw [shiftAction, aeval_eq_sum_range' hD]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply,
    Pi.smul_apply, smul_eq_mul, sequenceShift_pow]

theorem shiftAction_zero_sequence {R : Type*} [CommRing R] (p : R[X]) :
    shiftAction p (0 : ℕ → R) = 0 := map_zero _

theorem shiftAction_X_sub_one {R : Type*} [CommRing R] (f : ℕ → R) :
    shiftAction (X - 1 : R[X]) f = difference f := by
  funext n
  simp only [shiftAction, map_sub, aeval_X, map_one, LinearMap.sub_apply,
    Module.End.one_apply, Pi.sub_apply, difference]
  rfl

theorem shiftAction_difference_power {R : Type*} [CommRing R] (f : ℕ → R) (s : ℕ) :
    shiftAction ((X - 1 : R[X]) ^ s) f = iteratedDifference s f := by
  induction s with
  | zero => simp [shiftAction, iteratedDifference]
  | succ s ih =>
    rw [pow_succ', shiftAction_mul, shiftAction_X_sub_one, ih]
    rfl

theorem shiftAction_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : R[X]) (f : ℕ → R) (n : ℕ) :
    shiftAction (p.map φ) (fun i => φ (f i)) n = φ (shiftAction p f n) := by
  rw [shiftAction_sum_of_degree_lt (p.map φ) _
      ((natDegree_map_le).trans_lt (Nat.lt_succ_self p.natDegree)),
    shiftAction_sum, map_sum]
  apply sum_congr rfl
  intro i _
  rw [coeff_map, map_mul]

theorem shiftAction_annihilates_polynomial {p g : ℚ[X]} {s : ℕ}
    (hdiv : (X - 1 : ℚ[X]) ^ s ∣ p) (hg : g.natDegree < s) :
    shiftAction p (fun n : ℕ => g.eval (n : ℚ)) = 0 := by
  have hdiff : shiftAction ((X - 1 : ℚ[X]) ^ s) (fun n : ℕ => g.eval (n : ℚ)) = 0 := by
    rw [shiftAction_difference_power]
    funext n
    exact polynomial_iteratedDifference_zero g le_rfl hg n
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, mul_comm, shiftAction_mul, hdiff, shiftAction_zero_sequence]

theorem X_sub_one_power_dvd_flatPolynomial (N : ℕ) (a : ℕ → ℕ) :
    ((X - 1 : ℤ[X]) ^ weightMass N a) ∣ flatPolynomial N a := by
  refine ⟨(C (-1)) ^ weightMass N a * flatQuotient N a, ?_⟩
  rw [flatPolynomial_factor]
  have heq : (1 - X : ℤ[X]) = C (-1) * (X - 1) := by simp
  rw [heq, mul_pow]
  ring

theorem flatPolynomial_annihilates (N : ℕ) (a : ℕ → ℕ) (g : ℚ[X])
    (hg : g.natDegree < weightMass N a) :
    shiftAction ((flatPolynomial N a).map (Int.castRingHom ℚ))
      (fun n : ℕ => g.eval (n : ℚ)) = 0 := by
  apply shiftAction_annihilates_polynomial (s := weightMass N a) _ hg
  have h := Polynomial.map_dvd (Int.castRingHom ℚ) (X_sub_one_power_dvd_flatPolynomial N a)
  simpa using h

theorem iteratedDifference_power_vanish {R : Type*} [Ring R] (k s : ℕ) (hks : k < s) :
    iteratedDifference s (fun n : ℕ => (n : R) ^ k) = 0 := by
  have heq : (fun n : ℕ => (n : R) ^ k) =
      newtonEval (fun j => (powerCoefficient k j : R)) := by
    funext n
    exact (newtonEval_powerCoefficient k n).symm
  rw [heq, iteratedDifference_newtonEval]
  funext n
  apply Finset.sum_eq_zero
  intro j _
  dsimp only
  rw [powerCoefficient_eq_zero (by omega), Nat.cast_zero, zero_mul]

theorem shiftAction_annihilates_of_difference {R : Type*} [CommRing R]
    (p : R[X]) (f : ℕ → R) (s : ℕ) (hdiv : (X - 1 : R[X]) ^ s ∣ p)
    (hdiff : iteratedDifference s f = 0) : shiftAction p f = 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, mul_comm, shiftAction_mul, shiftAction_difference_power, hdiff,
    shiftAction_zero_sequence]

theorem flatPolynomial_annihilates_power {R : Type*} [CommRing R]
    (N : ℕ) (a : ℕ → ℕ) (k : ℕ) (hk : k < weightMass N a) (c : R) :
    shiftAction ((flatPolynomial N a).map (Int.castRingHom R))
      (fun n : ℕ => c * (n : R) ^ k) = 0 := by
  let p := (flatPolynomial N a).map (Int.castRingHom R)
  have hdiv : (X - 1 : R[X]) ^ weightMass N a ∣ p := by
    have h := Polynomial.map_dvd (Int.castRingHom R) (X_sub_one_power_dvd_flatPolynomial N a)
    simpa only [Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one] using h
  have hz := shiftAction_annihilates_of_difference p (fun n : ℕ => (n : R) ^ k)
    (weightMass N a) hdiv (iteratedDifference_power_vanish k _ hk)
  change shiftAction p (c • (fun n : ℕ => (n : R) ^ k)) = 0
  rw [map_smul, hz, smul_zero]

end Erdos345
