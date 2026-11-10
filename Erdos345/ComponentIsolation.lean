import Erdos345.FlatCyclotomic
import Mathlib.RingTheory.Polynomial.IsIntegral

namespace Erdos345

open Finset Polynomial

theorem iteratedDifference_power_self {R : Type*} [CommRing R] (j n : ℕ) :
    iteratedDifference j (fun a : ℕ => (a : R) ^ j) n = (j.factorial : R) := by
  have hdiff := iteratedDifference_power_vanish (R := R) j (j + 1) (by omega)
  induction n with
  | zero =>
    rw [iteratedDifference_power_zero]
    simp only [powerCoefficient, Nat.stirlingSecond_self, mul_one]
  | succ n ih =>
    have hn := congrFun hdiff n
    change iteratedDifference j (fun a : ℕ => (a : R) ^ j) (n + 1) -
      iteratedDifference j (fun a : ℕ => (a : R) ^ j) n = 0 at hn
    exact (sub_eq_zero.mp hn).trans ih

theorem exponentialPower_top_filter {R : Type*} [CommRing R] (z : R) (j : ℕ) :
    shiftAction ((X - C z) ^ j) (exponentialPower z j) =
      (z ^ j * (j.factorial : R)) • exponentialPower z 0 := by
  rw [exponentialPower, exponential_difference_power]
  funext n
  simp only [Pi.smul_apply, smul_eq_mul, exponentialSequence, iteratedDifference_power_self,
    exponentialPower, pow_zero, mul_one]
  ring

theorem shiftAction_exponential {R : Type*} [CommRing R] (P : R[X]) (z : R) :
    shiftAction P (exponentialPower z 0) = P.eval z • exponentialPower z 0 := by
  funext n
  rw [shiftAction_sum, eval_eq_sum_range]
  simp only [Pi.smul_apply, smul_eq_mul, exponentialPower, exponentialSequence, pow_zero, mul_one]
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem shiftAction_annihilates_multiple {R : Type*} [CommRing R]
    (P Q : R[X]) (f : ℕ → R) (hdiv : P ∣ Q) (hP : shiftAction P f = 0) :
    shiftAction Q f = 0 := by
  obtain ⟨A, rfl⟩ := hdiv
  rw [mul_comm, shiftAction_mul, hP, shiftAction_zero_sequence]

noncomputable def complementFactor {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) : K[X] := by
  classical
  exact ∏ a ∈ (univ.erase i), (X - C (z a)) ^ m a

noncomputable def componentFilter {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) : K[X] :=
  complementFactor z m i * (X - C (z i)) ^ (m i - 1)

theorem complementFactor_monic {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) : (complementFactor z m i).Monic := by
  apply monic_prod_of_monic
  intro a _
  exact (monic_X_sub_C (z a)).pow (m a)

theorem componentFilter_monic {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) : (componentFilter z m i).Monic :=
  (complementFactor_monic z m i).mul ((monic_X_sub_C (z i)).pow (m i - 1))

theorem componentFilter_dvd {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) : componentFilter z m i ∣ linearFactorProduct z m := by
  classical
  have hp : (X - C (z i)) ^ (m i - 1) ∣ (X - C (z i)) ^ m i :=
    pow_dvd_pow _ (Nat.sub_le _ _)
  have heq : linearFactorProduct z m = complementFactor z m i * (X - C (z i)) ^ m i := by
    exact (prod_erase_mul _ _ (mem_univ i)).symm
  rw [heq, componentFilter]
  exact mul_dvd_mul_left _ hp

theorem componentFilter_top {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) :
    shiftAction (componentFilter z m i) (exponentialPower (z i) (m i - 1)) =
      ((z i ^ (m i - 1) * ((m i - 1).factorial : K)) * (complementFactor z m i).eval (z i)) •
        exponentialPower (z i) 0 := by
  rw [componentFilter, shiftAction_mul, exponentialPower_top_filter, map_smul,
    shiftAction_exponential, smul_smul]

theorem componentFilter_other {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i a : I) (j : Fin (m a))
    (hother : a ≠ i ∨ (j : ℕ) < m i - 1) :
    shiftAction (componentFilter z m i) (exponentialPower (z a) j) = 0 := by
  classical
  by_cases ha : a = i
  · subst a
    have hj := hother.resolve_left (by simp)
    apply shiftAction_annihilates_multiple ((X - C (z i)) ^ (m i - 1))
      (componentFilter z m i) (exponentialPower (z i) j)
    · exact dvd_mul_left _ _
    · exact exponentialPower_annihilate (z i) j (m i - 1) hj
  · have hd : (X - C (z a)) ^ m a ∣ componentFilter z m i := by
      have hd' : (X - C (z a)) ^ m a ∣ complementFactor z m i :=
        dvd_prod_of_mem (fun b => (X - C (z b)) ^ m b) (mem_erase.mpr ⟨ha, mem_univ a⟩)
      exact hd'.trans (dvd_mul_right _ _)
    exact shiftAction_annihilates_multiple _ _ _ hd
      (exponentialPower_annihilate (z a) j (m a) j.is_lt)

end Erdos345
