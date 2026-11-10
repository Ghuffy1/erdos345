import Erdos345.ShiftAction
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

namespace Erdos345

open Polynomial

def sequenceAnnihilator {R : Type*} [CommRing R] (f : ℕ → R) : Ideal R[X] where
  carrier := {p | shiftAction p f = 0}
  zero_mem' := by simp [shiftAction]
  add_mem' := by
    intro p q hp hq
    change shiftAction (p + q) f = 0
    rw [shiftAction_add, hp, hq, add_zero]
  smul_mem' := by
    intro p q hq
    change shiftAction (p * q) f = 0
    rw [shiftAction_mul, hq, shiftAction_zero_sequence]

noncomputable def minimalAnnihilator {K : Type*} [Field K] (f : ℕ → K) : K[X] := by
  classical
  exact normalize (Submodule.IsPrincipal.generator (sequenceAnnihilator f))

theorem minimalAnnihilator_dvd_iff {K : Type*} [Field K] (f : ℕ → K) (p : K[X]) :
    minimalAnnihilator f ∣ p ↔ shiftAction p f = 0 := by
  classical
  rw [minimalAnnihilator, normalize_dvd_iff,
    ← Submodule.IsPrincipal.mem_iff_generator_dvd (sequenceAnnihilator f)]
  rfl

theorem minimalAnnihilator_annihilates {K : Type*} [Field K] (f : ℕ → K) :
    shiftAction (minimalAnnihilator f) f = 0 :=
  (minimalAnnihilator_dvd_iff f _).mp dvd_rfl

theorem minimalAnnihilator_ne_zero {K : Type*} [Field K] (f : ℕ → K)
    (p : K[X]) (hp : p ≠ 0) (hf : shiftAction p f = 0) :
    minimalAnnihilator f ≠ 0 := by
  intro hz
  have hd := (minimalAnnihilator_dvd_iff f p).mpr hf
  rw [hz, zero_dvd_iff] at hd
  exact hp hd

theorem minimalAnnihilator_monic {K : Type*} [Field K] (f : ℕ → K)
    (p : K[X]) (hp : p ≠ 0) (hf : shiftAction p f = 0) :
    (minimalAnnihilator f).Monic := by
  classical
  have hn := minimalAnnihilator_ne_zero f p hp hf
  unfold minimalAnnihilator at hn ⊢
  exact monic_normalize (fun hz => hn (by rw [hz, normalize_zero]))

theorem minimalAnnihilator_natDegree_le {K : Type*} [Field K] (f : ℕ → K)
    (p : K[X]) (hp : p ≠ 0) (hf : shiftAction p f = 0) :
    (minimalAnnihilator f).natDegree ≤ p.natDegree :=
  (minimalAnnihilator_monic f p hp hf).natDegree_le_of_dvd hp
    ((minimalAnnihilator_dvd_iff f p).mpr hf)

theorem minimalAnnihilator_unique {K : Type*} [Field K] (f : ℕ → K)
    (p q : K[X]) (hp : p.Monic) (hq : q.Monic)
    (hpd : ∀ r : K[X], p ∣ r ↔ shiftAction r f = 0)
    (hqd : ∀ r : K[X], q ∣ r ↔ shiftAction r f = 0) : p = q := by
  apply eq_of_monic_of_dvd_of_natDegree_le hq hp
  · exact (hqd p).mpr ((hpd p).mp dvd_rfl)
  · exact hp.natDegree_le_of_dvd hq.ne_zero ((hpd q).mpr ((hqd q).mp dvd_rfl))

/-- A rational sequence annihilated by a monic integer polynomial has an
actual monic minimal annihilator over the integers. Its universal property
is over all rational polynomial annihilators. -/
theorem exists_integral_minimalAnnihilator (f : ℕ → ℚ) (P : ℤ[X]) (hP : P.Monic)
    (hf : shiftAction (P.map (Int.castRingHom ℚ)) f = 0) :
    ∃ C : ℤ[X], C.Monic ∧ C ∣ P ∧
      C.map (Int.castRingHom ℚ) = minimalAnnihilator f ∧
      ∀ Q : ℚ[X], C.map (Int.castRingHom ℚ) ∣ Q ↔ shiftAction Q f = 0 := by
  let : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  have hPm : (P.map (Int.castRingHom ℚ)).Monic := hP.map _
  have hmonic := minimalAnnihilator_monic f _ hPm.ne_zero hf
  have hdiv := (minimalAnnihilator_dvd_iff f _).mpr hf
  have hdiv' : minimalAnnihilator f ∣ P.map (algebraMap ℤ ℚ) := hdiv
  obtain ⟨C, hC⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hP hdiv'
  rw [hmonic.leadingCoeff, Polynomial.C_1, mul_one] at hC
  have hC' : C.map (Int.castRingHom ℚ) = minimalAnnihilator f := hC
  have hCm : C.Monic := monic_of_injective (Int.cast_injective (α := ℚ)) (hC' ▸ hmonic)
  refine ⟨C, hCm, ?_, hC', ?_⟩
  · exact hP.dvd_of_fraction_map_dvd_fraction_map hCm (hC ▸ hdiv')
  · intro Q
    rw [hC']
    exact minimalAnnihilator_dvd_iff f Q

end Erdos345
