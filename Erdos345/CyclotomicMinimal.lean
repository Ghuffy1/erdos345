import Erdos345.MinimalAnnihilatorBaseChange
import Erdos345.CyclotomicExpansion
import Erdos345.DilationAnnihilator
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace Erdos345

open Finset Polynomial

/-- A monic divisor of a finite product of monic prime powers is itself a
product of smaller powers of the same polynomials. -/
theorem monic_divisor_of_prime_product
    {K I : Type*} [Field K] (S : Finset I) (p : I → K[X]) (m : I → ℕ)
    (hp : ∀ i ∈ S, Prime (p i)) (hmonic : ∀ i ∈ S, (p i).Monic)
    (C : K[X]) (hC : C.Monic) (hdiv : C ∣ ∏ i ∈ S, p i ^ m i) :
    ∃ h : I → ℕ, (∀ i ∈ S, h i ≤ m i) ∧ C = ∏ i ∈ S, p i ^ h i := by
  classical
  induction S using Finset.induction_on generalizing C with
  | empty =>
    have heq : C = 1 := hC.eq_one_of_isUnit (isUnit_iff_dvd_one.mpr (by simpa using hdiv))
    exact ⟨fun _ => 0, by simp, by simpa using heq⟩
  | @insert a S ha ih =>
    rw [prod_insert ha] at hdiv
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    have hpa := hp a (mem_insert_self _ _)
    have hpaMonic := hmonic a (mem_insert_self _ _)
    obtain ⟨j, hj, hAj⟩ := (dvd_prime_pow hpa (m a)).mp hA
    have hAnorm : normalize A = p a ^ j := by
      rw [normalize_eq_normalize_iff_associated.mpr hAj, (hpaMonic.pow j).normalize_eq_self]
    have hprodMonic : (∏ i ∈ S, p i ^ m i).Monic := by
      apply monic_prod_of_monic
      intro i hi
      exact (hmonic i (mem_insert_of_mem hi)).pow (m i)
    have hBnz : B ≠ 0 := ne_zero_of_dvd_ne_zero hprodMonic.ne_zero hB
    obtain ⟨h, hhm, hhprod⟩ := ih
      (fun i hi => hp i (mem_insert_of_mem hi))
      (fun i hi => hmonic i (mem_insert_of_mem hi))
      (normalize B) (monic_normalize hBnz) (normalize_dvd_iff.mpr hB)
    refine ⟨Function.update h a j, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with heq | hi
      · subst i
        simpa only [Function.update_self] using hj
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
        exact hhm i hi
    · calc
        C = normalize C := hC.normalize_eq_self.symm
        _ = normalize A * normalize B := by rw [hAB, normalize_mul]
        _ = p a ^ j * ∏ i ∈ S, p i ^ h i := by rw [hAnorm, hhprod]
        _ = ∏ i ∈ insert a S, p i ^ Function.update h a j i := by
          rw [prod_insert ha, Function.update_self]
          congr 1
          apply prod_congr rfl
          intro i hi
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]

theorem monic_divisor_of_cyclotomicProduct
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n)
    (C : ℚ[X]) (hC : C.Monic)
    (hdiv : C ∣ (cyclotomicProduct S m).map (Int.castRingHom ℚ)) :
    ∃ h : ℕ → ℕ, (∀ n ∈ S, h n ≤ m n) ∧
      C = (cyclotomicProduct S h).map (Int.castRingHom ℚ) := by
  have hmap : (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      ∏ n ∈ S, (cyclotomic n ℚ) ^ m n := by
    simp only [cyclotomicProduct, Polynomial.map_prod, Polynomial.map_pow, map_cyclotomic]
  rw [hmap] at hdiv
  obtain ⟨h, hbound, heq⟩ := monic_divisor_of_prime_product S (fun n => cyclotomic n ℚ) m
    (fun n hn => (cyclotomic.irreducible_rat (hS n hn)).prime)
    (fun n _ => cyclotomic.monic n ℚ) C hC hdiv
  refine ⟨h, hbound, ?_⟩
  simpa only [cyclotomicProduct, Polynomial.map_prod, Polynomial.map_pow, map_cyclotomic] using heq

/-- The actual minimal recurrence retains a bounded multiplicity for each
original cyclotomic order. This is a construction, not a hypothesis. -/
theorem exists_minimal_cyclotomic_annihilator
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℚ)
    (hf : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℚ)) f = 0) :
    ∃ h : ℕ → ℕ, (∀ n ∈ S, h n ≤ m n) ∧
      (cyclotomicProduct S h).map (Int.castRingHom ℚ) = minimalAnnihilator f := by
  have hm : ((cyclotomicProduct S m).map (Int.castRingHom ℚ)).Monic :=
    (cyclotomicProduct_monic S m).map _
  obtain ⟨h, hh, heq⟩ := monic_divisor_of_cyclotomicProduct S m hS
    (minimalAnnihilator f) (minimalAnnihilator_monic f _ hm.ne_zero hf)
    ((minimalAnnihilator_dvd_iff f _).mpr hf)
  exact ⟨h, hh, heq.symm⟩

end Erdos345
