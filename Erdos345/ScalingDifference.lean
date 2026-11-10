import Erdos345.PolynomialReduction
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

namespace Erdos345

open Polynomial

/-- The leading-difference scaling argument works at every modulus, with no
large-characteristic assumption or loss from monomial denominators. -/
theorem reduction_scaling_difference {q k j : ℕ}
    (h : hasIntegerPolynomialReduction q k j) (a : ℕ) :
    (q : ℤ) ∣ (powerCoefficient k j : ℤ) * ((a : ℤ) ^ j - (a : ℤ) ^ k) := by
  classical
  obtain ⟨p, hp, _hInt, hmod⟩ := h
  let f : ℕ → ℤ := fun n => Classical.choose (hmod n)
  have hf : ∀ n : ℕ, p.eval (n : ℚ) = (f n : ℚ) ∧
      (q : ℤ) ∣ (n : ℤ) ^ k - f n := by
    intro n
    exact Classical.choose_spec (hmod n)
  let r : ℕ → ℤ := fun n => f (a * n) - (a : ℤ) ^ k * f n
  let R : ℚ[X] := p.comp (C (a : ℚ) * X) - C ((a : ℚ) ^ k) * p
  have hdivr : ∀ n : ℕ, (q : ℤ) ∣ r n := by
    intro n
    have hm := dvd_mul_of_dvd_right (hf n).2 ((a : ℤ) ^ k)
    have hs := dvd_sub hm (hf (a * n)).2
    have he :
        (a : ℤ) ^ k * ((n : ℤ) ^ k - f n) -
          (((a * n : ℕ) : ℤ) ^ k - f (a * n)) = r n := by
      dsimp [r]
      ring
    rwa [he] at hs
  have hlin : (C (a : ℚ) * X).natDegree ≤ 1 := by
    simpa using natDegree_C_mul_le (a : ℚ) (X : ℚ[X])
  have hcomp : (p.comp (C (a : ℚ) * X)).natDegree ≤ j := by
    have hc := (natDegree_comp_le (p := p) (q := C (a : ℚ) * X)).trans
      (Nat.mul_le_mul hp hlin)
    simpa only [Nat.mul_one] using hc
  have hRdeg : R.natDegree ≤ j :=
    (natDegree_sub_le _ _).trans (max_le hcomp ((natDegree_C_mul_le _ p).trans hp))
  have hRval : ∀ n : ℕ, R.eval (n : ℚ) = (r n : ℚ) := by
    intro n
    calc
      R.eval (n : ℚ) =
          p.eval ((a * n : ℕ) : ℚ) - (a : ℚ) ^ k * p.eval (n : ℚ) := by
        simp only [R, eval_sub, eval_comp, eval_mul, eval_C, eval_X, Nat.cast_mul]
      _ = (f (a * n) : ℚ) - (a : ℚ) ^ k * (f n : ℚ) := by
        rw [(hf (a * n)).1, (hf n).1]
      _ = (r n : ℚ) := by simp only [r, Int.cast_sub, Int.cast_mul, Int.cast_pow,
          Int.cast_natCast]
  have hQ : (fun n : ℕ => (f n : ℚ)) = (fun n : ℕ => p.eval (n : ℚ)) := by
    funext n
    exact (hf n).1.symm
  have hQR : (fun n : ℕ => (r n : ℚ)) = (fun n : ℕ => R.eval (n : ℚ)) := by
    funext n
    exact (hRval n).symm
  have htop :
      ((iteratedDifference j f 0 : ℤ) : ℚ) = (j.factorial : ℚ) * p.coeff j := by
    have hm := map_iteratedDifference (Int.castRingHom ℚ) f j 0
    change ((iteratedDifference j f 0 : ℤ) : ℚ) =
      iteratedDifference j (fun n : ℕ => (f n : ℚ)) 0 at hm
    rw [hQ, polynomial_top_difference p hp] at hm
    exact hm
  have htopR :
      ((iteratedDifference j r 0 : ℤ) : ℚ) =
        ((iteratedDifference j f 0 : ℤ) : ℚ) * ((a : ℚ) ^ j - (a : ℚ) ^ k) := by
    have hm := map_iteratedDifference (Int.castRingHom ℚ) r j 0
    change ((iteratedDifference j r 0 : ℤ) : ℚ) =
      iteratedDifference j (fun n : ℕ => (r n : ℚ)) 0 at hm
    rw [hQR, polynomial_top_difference R hRdeg] at hm
    rw [hm, htop]
    simp only [R, coeff_sub, comp_C_mul_X_coeff, coeff_C_mul]
    ring
  have htopRint :
      iteratedDifference j r 0 =
        iteratedDifference j f 0 * ((a : ℤ) ^ j - (a : ℤ) ^ k) := by
    exact_mod_cast htopR
  have hr := dvd_iteratedDifference (q : ℤ) r hdivr j 0
  rw [htopRint] at hr
  have ha := dvd_iteratedDifference (q : ℤ)
    (fun n : ℕ => (n : ℤ) ^ k - f n) (fun n => (hf n).2) j 0
  rw [iteratedDifference_sub, iteratedDifference_power_zero] at ha
  have hm := dvd_mul_of_dvd_left ha ((a : ℤ) ^ j - (a : ℤ) ^ k)
  have hs := dvd_add hm hr
  have he :
      ((powerCoefficient k j : ℤ) - iteratedDifference j f 0) *
          ((a : ℤ) ^ j - (a : ℤ) ^ k) +
        iteratedDifference j f 0 * ((a : ℤ) ^ j - (a : ℤ) ^ k) =
      (powerCoefficient k j : ℤ) * ((a : ℤ) ^ j - (a : ℤ) ^ k) := by ring
  rwa [he] at hs

theorem reductionModulus_scaling_difference {q k j : ℕ}
    (h : q ∣ reductionModulus k j) (a : ℕ) :
    (q : ℤ) ∣ (powerCoefficient k j : ℤ) * ((a : ℤ) ^ j - (a : ℤ) ^ k) :=
  reduction_scaling_difference ((hasIntegerPolynomialReduction_iff_dvd q k j).mpr h) a

end Erdos345
