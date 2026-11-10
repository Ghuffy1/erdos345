import Erdos345.MinimalAnnihilator
import Erdos345.RecurrenceCongruence
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

namespace Erdos345

open Finset Polynomial

def initialShiftFamily {R : Type*} (f : ℕ → R) (D d : ℕ) : Fin d → Fin D → R :=
  fun i n => f ((n : ℕ) + i)

theorem shiftAction_monomial {R : Type*} [CommRing R]
    (f : ℕ → R) (i n : ℕ) (c : R) :
    shiftAction (monomial i c) f n = c * f (n + i) := by
  simp only [shiftAction, aeval_monomial, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul, sequenceShift_pow]

theorem shiftAction_ofFn {R : Type*} [CommRing R] [DecidableEq R]
    (f : ℕ → R) (d n : ℕ) (c : Fin d → R) :
    shiftAction (ofFn d c) f n = ∑ i, c i * f (n + i) := by
  rw [ofFn_eq_sum_monomial]
  simp only [shiftAction, map_sum, LinearMap.sum_apply, Finset.sum_apply]
  apply sum_congr rfl
  intro i _
  exact shiftAction_monomial f i n (c i)

theorem initialShiftFamily_linearIndependent {K : Type*} [Field K]
    (f : ℕ → K) (P : K[X]) (hP : P.Monic) (hf : shiftAction P f = 0) :
    LinearIndependent K (initialShiftFamily f P.natDegree (minimalAnnihilator f).natDegree) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let Q := ofFn (minimalAnnihilator f).natDegree c
  have hrec : shiftAction P (shiftAction Q f) = 0 := by
    rw [← shiftAction_mul, mul_comm P Q, shiftAction_mul, hf, shiftAction_zero_sequence]
  have hinit : ∀ n < P.natDegree, shiftAction Q f n = 0 := by
    intro n hn
    have hv := congrFun hc ⟨n, hn⟩
    simpa only [Q, shiftAction_ofFn, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, initialShiftFamily, Pi.zero_apply] using hv
  have hQann := zero_of_recurrence_initial P P.natDegree le_rfl
    (by simp only [coeff_natDegree, hP.leadingCoeff, one_pow])
    (shiftAction Q f) hrec hinit
  have hdvd := (minimalAnnihilator_dvd_iff f Q).mpr hQann
  have hQ : Q = 0 := by
    by_contra hnz
    have hdegree := (minimalAnnihilator_monic f P hP.ne_zero hf).natDegree_le_of_dvd hnz hdvd
    have hsmall : Q.natDegree < (minimalAnnihilator f).natDegree :=
      ofFn_natDegree_lt (by have := i.is_lt; omega) c
    omega
  have hcoeff := congrArg (fun p : K[X] => p.coeff i) hQ
  simpa only [Q, ofFn_coeff_eq_val_of_lt c i.is_lt, coeff_zero] using hcoeff

theorem no_small_annihilator_of_initial_independent
    {K : Type*} [Field K] (f : ℕ → K) (D d : ℕ)
    (hli : LinearIndependent K (initialShiftFamily f D d))
    (Q : K[X]) (hdeg : Q.natDegree < d) (hQ : shiftAction Q f = 0) : Q = 0 := by
  classical
  have hc : ∑ i, (toFn d Q) i • initialShiftFamily f D d i = 0 := by
    funext n
    have hv := congrFun hQ n
    rw [← ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg, shiftAction_ofFn] at hv
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, initialShiftFamily,
      Pi.zero_apply] using hv
  have hz := Fintype.linearIndependent_iff.mp hli (toFn d Q) hc
  have hzero : toFn d Q = 0 := funext hz
  rw [← ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg, hzero, map_zero]

theorem shiftAction_map_annihilates {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : ℕ → K) (P : K[X]) (hP : shiftAction P f = 0) :
    shiftAction (P.map (algebraMap K L)) (fun n => algebraMap K L (f n)) = 0 := by
  funext n
  simp only [shiftAction_map, congrFun hP n, Pi.zero_apply, map_zero]

/-- The minimal recurrence polynomial of a sequence over a field is unchanged
after extending scalars. A finite initial block detects all relations. -/
theorem minimalAnnihilator_map {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : ℕ → K) (P : K[X]) (hP : P.Monic) (hf : shiftAction P f = 0) :
    (minimalAnnihilator f).map (algebraMap K L) =
      minimalAnnihilator (fun n => algebraMap K L (f n)) := by
  classical
  let fL : ℕ → L := fun n => algebraMap K L (f n)
  have hCm := minimalAnnihilator_monic f P hP.ne_zero hf
  have hCann := shiftAction_map_annihilates f (minimalAnnihilator f)
    (minimalAnnihilator_annihilates f) (L := L)
  have hRm := minimalAnnihilator_monic fL _ (hCm.map (algebraMap K L)).ne_zero hCann
  have hdiv := (minimalAnnihilator_dvd_iff fL _).mpr hCann
  apply eq_of_monic_of_dvd_of_natDegree_le hRm (hCm.map (algebraMap K L)) hdiv
  rw [hCm.natDegree_map]
  by_contra hle
  have hdeg : (minimalAnnihilator fL).natDegree < (minimalAnnihilator f).natDegree := by omega
  have hli := initialShiftFamily_linearIndependent f P hP hf
  have hliL : LinearIndependent L
      (initialShiftFamily fL P.natDegree (minimalAnnihilator f).natDegree) := by
    exact (linearIndependent_algebraMap_comp_iff (S := L)).mpr hli
  have hz := no_small_annihilator_of_initial_independent fL P.natDegree
    (minimalAnnihilator f).natDegree hliL (minimalAnnihilator fL) hdeg
    (minimalAnnihilator_annihilates fL)
  exact hRm.ne_zero hz

end Erdos345
