import Erdos345.CyclotomicMinimal

namespace Erdos345

open Finset Polynomial

/-- Every root in a minimal split recurrence has a nonzero coefficient at its
highest prescribed polynomial degree. Otherwise its factor can be lowered. -/
theorem minimal_split_expansion_top_ne_zero
    {K I : Type*} [Field K] [Fintype I] (z : I → K) (m : I → ℕ)
    (f : ℕ → K) (hminimal : linearFactorProduct z m = minimalAnnihilator f)
    (c : (Σ i, Fin (m i)) → K)
    (hrep : f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2)
    (i : I) (hmi : 0 < m i) :
    c ⟨i, ⟨m i - 1, by omega⟩⟩ ≠ 0 := by
  classical
  intro hzero
  let m' : I → ℕ := Function.update m i (m i - 1)
  let Q := linearFactorProduct z m'
  have hQann : shiftAction Q f = 0 := by
    rw [hrep, map_sum]
    apply sum_eq_zero
    rintro ⟨a, j⟩ _
    by_cases hc : c ⟨a, j⟩ = 0
    · rw [hc, zero_smul, map_zero]
    · have hj : (j : ℕ) < m' a := by
        by_cases ha : a = i
        · subst a
          have hlast : (j : ℕ) ≠ m i - 1 := by
            intro heq
            have hjeq : j = ⟨m i - 1, by omega⟩ := Fin.ext heq
            exact hc (hjeq ▸ hzero)
          simp only [m', Function.update_self]
          have := j.is_lt
          omega
        · simpa only [m', Function.update_of_ne ha] using j.is_lt
      have hkill : shiftAction Q (exponentialPower (z a) j) = 0 :=
        linearFactorProduct_annihilates_component z m' a ⟨j, hj⟩
      rw [map_smul, hkill, smul_zero]
  have hdvd : linearFactorProduct z m ∣ Q := by
    rw [hminimal]
    exact (minimalAnnihilator_dvd_iff f Q).mpr hQann
  have hdegree := (linearFactorProduct_monic z m).natDegree_le_of_dvd
    (linearFactorProduct_monic z m').ne_zero hdvd
  have hstrict : (∑ a, m' a) < ∑ a, m a := by
    apply sum_lt_sum
    · intro a _
      by_cases ha : a = i
      · subst a
        simp only [m', Function.update_self]
        omega
      · simp only [m', Function.update_of_ne ha, le_refl]
    · refine ⟨i, mem_univ i, ?_⟩
      simp only [m', Function.update_self]
      omega
  change (linearFactorProduct z m).natDegree ≤ (linearFactorProduct z m').natDegree at hdegree
  rw [linearFactorProduct_natDegree, linearFactorProduct_natDegree] at hdegree
  omega

theorem minimal_cyclotomic_expansion_top_ne_zero
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℚ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (i : CyclotomicRootIndex S) (hmi : 0 < cyclotomicRootMultiplicity m i) :
    c ⟨i, ⟨cyclotomicRootMultiplicity m i - 1, by omega⟩⟩ ≠ 0 := by
  have hann : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℚ)) f = 0 := by
    rw [hminimal]
    exact minimalAnnihilator_annihilates f
  have hbase := minimalAnnihilator_map (L := ℂ) f
    ((cyclotomicProduct S m).map (Int.castRingHom ℚ))
    ((cyclotomicProduct_monic S m).map _) hann
  change (minimalAnnihilator f).map (algebraMap ℚ ℂ) =
    minimalAnnihilator (fun n => (f n : ℂ)) at hbase
  have hsplit : linearFactorProduct (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m) =
      minimalAnnihilator (fun n => (f n : ℂ)) := by
    rw [cyclotomicProduct_split S m hS]
    rw [← hbase, ← hminimal, Polynomial.map_map]
    rfl
  exact minimal_split_expansion_top_ne_zero (@cyclotomicRootValue S)
    (cyclotomicRootMultiplicity m) (fun n => (f n : ℂ)) hsplit c hrep i hmi

end Erdos345
