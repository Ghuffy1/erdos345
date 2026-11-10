import Erdos345.FiniteExpectation
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

namespace Erdos345

open scoped ComplexConjugate

theorem cyclic_character_sum {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ h : ZMod q, ZMod.stdAddChar (h * x)) = if x = 0 then (q : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · rw [ite_eq_right hx]
    have h := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hx)
    simpa only [AddChar.mulShift_apply, mul_comm] using h

noncomputable def cyclicFourier {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (h : ZMod q) : ℂ :=
  ∑ x : ZMod q, f x * ZMod.stdAddChar (h * x)

theorem cyclicFourier_zero {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    cyclicFourier f 0 = ∑ x, f x := by simp [cyclicFourier]

theorem cyclic_character_pair {q : ℕ} [NeZero q] (h x y : ZMod q) (a b : ℂ) :
    (a * ZMod.stdAddChar (h * x)) * conj (b * ZMod.stdAddChar (h * y)) =
      (a * conj b) * ZMod.stdAddChar (h * (x - y)) := by
  rw [map_mul (starRingEnd ℂ) b (ZMod.stdAddChar (h * y))]
  rw [← AddChar.map_neg_eq_conj (ZMod.stdAddChar : AddChar (ZMod q) ℂ) (h * y)]
  have heq : h * (x - y) = h * x + -(h * y) := by ring
  rw [heq, AddChar.map_add_eq_mul]
  ring

/-- Parseval on the actual finite cyclic group, with the unnormalized
Fourier transform. This will connect subset probabilities to support. -/
theorem cyclic_parseval_complex {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ h : ZMod q, cyclicFourier f h * conj (cyclicFourier f h)) =
      (q : ℂ) * ∑ x : ZMod q, f x * conj (f x) := by
  classical
  have hexpand (h : ZMod q) : cyclicFourier f h * conj (cyclicFourier f h) =
      ∑ x : ZMod q, ∑ y : ZMod q, (f x * conj (f y)) * ZMod.stdAddChar (h * (x - y)) := by
    unfold cyclicFourier
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact cyclic_character_pair h x y (f x) (f y)
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : ZMod q, ∑ y : ZMod q,
        (f x * conj (f y)) * (∑ h : ZMod q, ZMod.stdAddChar (h * (x - y))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod q, (q : ℂ) * (f x * conj (f x)) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [cyclic_character_sum, sub_eq_zero, mul_ite, mul_zero]
      simp [mul_comm]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem cyclic_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ h : ZMod q, ‖cyclicFourier f h‖ ^ 2) = (q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have h := cyclic_parseval_complex f
  simp only [Complex.mul_conj'] at h
  exact_mod_cast h

end Erdos345
