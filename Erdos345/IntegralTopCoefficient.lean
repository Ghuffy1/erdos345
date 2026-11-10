import Erdos345.ComponentIsolation

namespace Erdos345

open Finset Polynomial

theorem componentFilter_expansion_at_zero
    {K I : Type*} [Field K] [Fintype I] (z : I → K) (m : I → ℕ)
    (f : ℕ → K) (c : (Σ i, Fin (m i)) → K)
    (hrep : f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2)
    (i : I) (hmi : 0 < m i) :
    shiftAction (componentFilter z m i) f 0 =
      c ⟨i, ⟨m i - 1, by omega⟩⟩ *
        ((z i ^ (m i - 1) * ((m i - 1).factorial : K)) *
          (complementFactor z m i).eval (z i)) := by
  classical
  let last : (Σ a, Fin (m a)) := ⟨i, ⟨m i - 1, by omega⟩⟩
  have hother (aj : Σ a, Fin (m a)) (hne : aj ≠ last) :
      aj.1 ≠ i ∨ (aj.2 : ℕ) < m i - 1 := by
    rcases aj with ⟨a, j⟩
    by_cases ha : a = i
    · subst a
      apply Or.inr
      have hjne : (j : ℕ) ≠ m i - 1 := by
        intro hj
        have hjeq : j = ⟨m i - 1, by omega⟩ := Fin.ext hj
        apply hne
        simp only [last, hjeq]
      have := j.is_lt
      change (j : ℕ) < m i - 1
      omega
    · exact Or.inl ha
  rw [hrep, map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single last]
  · dsimp only [last]
    rw [map_smul, componentFilter_top]
    simp only [Pi.smul_apply, smul_eq_mul, exponentialPower, exponentialSequence,
      pow_zero, mul_one]
  · intro aj _ hne
    rw [map_smul, componentFilter_other z m i aj.1 aj.2 (hother aj hne), smul_zero]
    rfl
  · simp

theorem isIntegral_shiftAction {K : Type*} [Field K] [Algebra ℤ K]
    (P : K[X]) (f : ℕ → K)
    (hcoeff : ∀ j, IsIntegral ℤ (P.coeff j)) (hf : ∀ n, IsIntegral ℤ (f n)) (n : ℕ) :
    IsIntegral ℤ (shiftAction P f n) := by
  rw [shiftAction_sum]
  exact IsIntegral.sum _ (fun j _ => (hcoeff j).mul (hf (n + j)))

/-- The denominator-cleared top component is an algebraic integer. This uses
an integral polynomial filter and avoids assuming that each conjugate of an
algebraic integer has absolute value at least one. -/
theorem filtered_top_isIntegral
    {I : Type*} [Fintype I] (z : I → ℂ) (m : I → ℕ)
    (C : ℤ[X]) (hC : C.Monic)
    (hsplit : linearFactorProduct z m = C.map (Int.castRingHom ℂ))
    (f : ℕ → ℂ) (hf : ∀ n, IsIntegral ℤ (f n))
    (c : (Σ i, Fin (m i)) → ℂ)
    (hrep : f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2)
    (i : I) (hmi : 0 < m i) :
    IsIntegral ℤ (c ⟨i, ⟨m i - 1, by omega⟩⟩ *
      ((z i ^ (m i - 1) * ((m i - 1).factorial : ℂ)) *
        (complementFactor z m i).eval (z i))) := by
  have hdiv : componentFilter z m i ∣ C.map (Int.castRingHom ℂ) :=
    hsplit ▸ componentFilter_dvd z m i
  have hcoeff : ∀ j, IsIntegral ℤ ((componentFilter z m i).coeff j) :=
    fun j => Polynomial.isIntegral_coeff_of_dvd C (componentFilter z m i) hC
      (componentFilter_monic z m i) hdiv j
  have hv := isIntegral_shiftAction (componentFilter z m i) f hcoeff hf 0
  rwa [componentFilter_expansion_at_zero z m f c hrep i hmi] at hv

theorem complementFactor_eval_ne_zero
    {K I : Type*} [Field K] [Fintype I] (z : I → K) (m : I → ℕ)
    (hinj : Function.Injective z) (i : I) : (complementFactor z m i).eval (z i) ≠ 0 := by
  classical
  rw [complementFactor, eval_prod]
  apply prod_ne_zero_iff.mpr
  intro a ha
  rw [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => (mem_erase.mp ha).1 (hinj he).symm))

theorem filtered_top_ne_zero
    {K I : Type*} [Field K] [CharZero K] [Fintype I] (z : I → K) (m : I → ℕ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0)
    (f : ℕ → K) (hminimal : linearFactorProduct z m = minimalAnnihilator f)
    (c : (Σ i, Fin (m i)) → K)
    (hrep : f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2)
    (i : I) (hmi : 0 < m i) :
    c ⟨i, ⟨m i - 1, by omega⟩⟩ *
      ((z i ^ (m i - 1) * ((m i - 1).factorial : K)) *
        (complementFactor z m i).eval (z i)) ≠ 0 := by
  exact mul_ne_zero (minimal_split_expansion_top_ne_zero z m f hminimal c hrep i hmi)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hz i))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) (complementFactor_eval_ne_zero z m hinj i))

end Erdos345
