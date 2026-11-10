import Erdos345.CofactorWitness
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace Erdos345

open Finset Polynomial

theorem cyclotomic_resultant_eq_product (t : ℕ) (ht : 0 < t) (A : ℤ[X]) :
    ((resultant (cyclotomic t ℤ) A : ℤ) : ℂ) =
      ∏ z ∈ primitiveRoots t ℂ, A.eval₂ (Int.castRingHom ℂ) z := by
  let φ : ℤ →+* ℂ := Int.castRingHom ℂ
  let : NeZero (t : ℂ) := ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)⟩
  have hdegree : ((cyclotomic t ℤ).map φ).natDegree = (cyclotomic t ℤ).natDegree :=
    (cyclotomic.monic t ℤ).natDegree_map φ
  have hres := resultant_eq_prod_eval ((cyclotomic t ℤ).map φ) (A.map φ)
    A.natDegree natDegree_map_le (IsAlgClosed.splits _)
  rw [hdegree, resultant_map_map, (cyclotomic.monic t ℤ).map φ |>.leadingCoeff,
    one_pow, one_mul, map_cyclotomic, cyclotomic.roots_eq_primitiveRoots_val] at hres
  change φ (resultant (cyclotomic t ℤ) A) = _
  rw [hres]
  simp only [eval_map, φ]
  rfl

theorem one_le_norm_intCast (a : ℤ) (ha : a ≠ 0) : (1 : ℝ) ≤ ‖(a : ℂ)‖ := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  have h : (1 : ℤ) ≤ |a| := by have := abs_pos.mpr ha; omega
  exact_mod_cast h

/-- The norm argument is over all primitive conjugates. It does not impose
a lower bound on each individual conjugate. -/
theorem primitive_value_norm_product_ge_one
    (t : ℕ) (ht : 0 < t) (A : ℤ[X])
    (hA : ∀ z ∈ primitiveRoots t ℂ, A.eval₂ (Int.castRingHom ℂ) z ≠ 0) :
    (1 : ℝ) ≤ ∏ z ∈ primitiveRoots t ℂ, ‖A.eval₂ (Int.castRingHom ℂ) z‖ := by
  have hp : (∏ z ∈ primitiveRoots t ℂ, A.eval₂ (Int.castRingHom ℂ) z) ≠ 0 :=
    prod_ne_zero_iff.mpr hA
  have heq := cyclotomic_resultant_eq_product t ht A
  have hres : resultant (cyclotomic t ℤ) A ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at heq
    exact hp heq.symm
  have hnorm := one_le_norm_intCast _ hres
  rwa [heq, norm_prod] at hnorm

end Erdos345
