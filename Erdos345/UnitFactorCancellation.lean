import Erdos345.RecurrenceCongruence
import Mathlib.RingTheory.Coprime.Lemmas

namespace Erdos345

open Polynomial

theorem isCoprime_linear_of_eval_unit {R : Type*} [CommRing R]
    (Q : R[X]) (x : R) (hunit : IsUnit (Q.eval x)) :
    IsCoprime (X - C x) Q := by
  obtain ⟨u, hu⟩ := hunit
  have hdiv : (X - C x) ∣ Q - C (Q.eval x) := X_sub_C_dvd_sub_C_eval
  obtain ⟨S, hS⟩ := hdiv
  have hQ : Q = (X - C x) * S + C (Q.eval x) := sub_eq_iff_eq_add.mp hS
  let b : R := ↑(u⁻¹)
  refine ⟨-C b * S, C b, ?_⟩
  calc
    (-C b * S) * (X - C x) + C b * Q =
        C b * C (Q.eval x) := by
      conv_lhs => rw [hQ]
      ring
    _ = 1 := by rw [← hu, ← map_mul]; simp [b]

/-- A factor invertible at one can be canceled on a sequence with a nilpotent
forward difference. This is valid in every commutative ring. -/
theorem cancel_unit_factor_on_polynomial_sequence {R : Type*} [CommRing R]
    (P Q : R[X]) (f : ℕ → R) (s : ℕ)
    (hunit : IsUnit (Q.eval 1)) (hdiff : iteratedDifference s f = 0)
    (hproduct : shiftAction (P * Q) f = 0) :
    shiftAction P f = 0 := by
  have hcop : IsCoprime ((X - 1 : R[X]) ^ s) Q := by
    simpa only [map_one] using (isCoprime_linear_of_eval_unit Q 1 hunit).pow_left (m := s)
  obtain ⟨A, B, hAB⟩ := hcop
  have hP : P = (A * P) * (X - 1) ^ s + B * (P * Q) := by
    calc
      P = 1 * P := by rw [one_mul]
      _ = (A * (X - 1) ^ s + B * Q) * P := by rw [hAB]
      _ = _ := by ring
  rw [hP, shiftAction_add, shiftAction_mul, shiftAction_difference_power, hdiff,
    shiftAction_zero_sequence, shiftAction_mul, hproduct, shiftAction_zero_sequence, add_zero]

/-- Unit factors can be removed from an integer polynomial annihilator modulo
an arbitrary natural modulus. Nilpotence here is proved for the actual power
sequence; the unit value is an explicit arithmetic condition. -/
theorem remove_unit_factor_from_power_annihilator (P Q : ℤ[X]) (q k : ℕ)
    (hunit : IsUnit ((Q.eval 1 : ℤ) : ZMod q))
    (hproduct : ∀ n, (q : ℤ) ∣ shiftAction (P * Q) (fun j : ℕ => (j : ℤ) ^ k) n) :
    ∀ n, (q : ℤ) ∣ shiftAction P (fun j : ℕ => (j : ℤ) ^ k) n := by
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  let f : ℕ → ZMod q := fun j => φ ((j : ℤ) ^ k)
  have hnil : iteratedDifference (k + 1) f = 0 := by
    funext n
    change iteratedDifference (k + 1) (fun j => φ ((j : ℤ) ^ k)) n = 0
    rw [← map_iteratedDifference]
    have hzero := congrFun (iteratedDifference_power_vanish (R := ℤ) k (k + 1) (by omega)) n
    rw [hzero]
    simp
  have hQunit : IsUnit ((Q.map φ).eval 1) := by
    rw [eval_one_map]
    exact hunit
  have hprod : shiftAction (P.map φ * Q.map φ) f = 0 := by
    funext n
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hproduct n)
    change φ (shiftAction (P * Q) (fun j : ℕ => (j : ℤ) ^ k) n) = 0 at hz
    rw [← shiftAction_map, Polynomial.map_mul] at hz
    exact hz
  have hrem := cancel_unit_factor_on_polynomial_sequence (P.map φ) (Q.map φ) f
    (k + 1) hQunit hnil hprod
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  have hz := congrFun hrem n
  change shiftAction (P.map φ) (fun j => φ ((j : ℤ) ^ k)) n = 0 at hz
  rw [shiftAction_map] at hz
  exact hz

end Erdos345
