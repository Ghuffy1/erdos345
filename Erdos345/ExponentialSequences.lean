import Erdos345.CyclotomicDilation
import Erdos345.FlatMoments
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace Erdos345

open Finset Polynomial

noncomputable def exponentialSequence {R : Type*} [CommRing R]
    (z : R) (f : ℕ → R) : ℕ → R := fun n => z ^ n * f n

noncomputable def exponentialPower {R : Type*} [CommRing R]
    (z : R) (j : ℕ) : ℕ → R := exponentialSequence z (fun n => (n : R) ^ j)

theorem shiftAction_sub {R : Type*} [CommRing R] (p q : R[X]) (f : ℕ → R) :
    shiftAction (p - q) f = shiftAction p f - shiftAction q f := by
  simp only [shiftAction, map_sub, LinearMap.sub_apply]

theorem shiftAction_X {R : Type*} [CommRing R] (f : ℕ → R) :
    shiftAction (X : R[X]) f = fun n => f (n + 1) := by
  simp only [shiftAction, aeval_X]
  rfl

theorem exponential_difference {R : Type*} [CommRing R] (z : R) (f : ℕ → R) :
    shiftAction (X - C z) (exponentialSequence z f) =
      z • exponentialSequence z (difference f) := by
  rw [shiftAction_sub, shiftAction_X, shiftAction_C]
  funext n
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, exponentialSequence, difference,
    pow_succ]
  ring

theorem exponential_difference_power {R : Type*} [CommRing R]
    (z : R) (f : ℕ → R) (s : ℕ) :
    shiftAction ((X - C z) ^ s) (exponentialSequence z f) =
      z ^ s • exponentialSequence z (iteratedDifference s f) := by
  induction s with
  | zero => simp [shiftAction, iteratedDifference]
  | succ s ih =>
    rw [pow_succ', shiftAction_mul, ih, map_smul, exponential_difference, smul_smul]
    rw [pow_succ]
    rfl

theorem exponentialPower_annihilate {R : Type*} [CommRing R]
    (z : R) (j s : ℕ) (hjs : j < s) :
    shiftAction ((X - C z) ^ s) (exponentialPower z j) = 0 := by
  rw [exponentialPower, exponential_difference_power, iteratedDifference_power_vanish j s hjs]
  funext n
  simp [exponentialSequence]

theorem exponentialPower_top_difference {R : Type*} [CommRing R]
    (z : R) (j : ℕ) :
    shiftAction ((X - C z) ^ j) (exponentialPower z j) 0 = z ^ j * (j.factorial : R) := by
  rw [exponentialPower, exponential_difference_power]
  simp only [Pi.smul_apply, smul_eq_mul, exponentialSequence, pow_zero, one_mul,
    iteratedDifference_power_zero]
  simp [powerCoefficient, Nat.stirlingSecond_self]

theorem exponentialPower_dilate {R : Type*} [CommRing R] (z : R) (j g : ℕ) :
    (fun n : ℕ => exponentialPower z j (g * n)) =
      (g : R) ^ j • exponentialPower (z ^ g) j := by
  funext n
  simp only [exponentialPower, exponentialSequence, Nat.cast_mul, mul_pow,
    Pi.smul_apply, smul_eq_mul, ← pow_mul]
  ring

theorem exponentialPower_linearIndependent {K : Type*} [Field K] [CharZero K]
    (z : K) (hz : z ≠ 0) (m : ℕ) :
    LinearIndependent K (fun j : Fin m => exponentialPower z j) := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ m ih =>
    apply linearIndependent_finSucc'.mpr
    constructor
    · change LinearIndependent K (fun j : Fin m => exponentialPower z j)
      exact ih
    · let L : Module.End K (ℕ → K) := shiftAction ((X - C z) ^ m)
      have hspan : Submodule.span K
          (Set.range (Fin.init (fun j : Fin (m + 1) => exponentialPower z j))) ≤ LinearMap.ker L := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact exponentialPower_annihilate z j m j.is_lt
      intro hmem
      have hzero := hspan hmem
      change shiftAction ((X - C z) ^ m) (exponentialPower z m) = 0 at hzero
      have hval := congrFun hzero 0
      rw [exponentialPower_top_difference] at hval
      change z ^ m * (m.factorial : K) = 0 at hval
      exact (mul_ne_zero (pow_ne_zero _ hz) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))) hval

end Erdos345
