import Erdos345.CyclotomicResultant

namespace Erdos345

open Finset Polynomial

theorem cyclotomicProduct_degree_pos
    (S : Finset ℕ) (m : ℕ → ℕ) {t : ℕ} (ht : t ∈ S) (ht0 : 0 < t) (hm : 0 < m t) :
    0 < (cyclotomicProduct S m).natDegree := by
  have hdvd : (cyclotomic t ℤ) ^ m t ∣ cyclotomicProduct S m := dvd_prod_of_mem _ ht
  have hdegree := ((cyclotomic.monic t ℤ).pow (m t)).natDegree_le_of_dvd
    (cyclotomicProduct_monic S m).ne_zero hdvd
  have hpos : 0 < ((cyclotomic t ℤ) ^ m t).natDegree := by
    rw [natDegree_pow, natDegree_cyclotomic]
    exact Nat.mul_pos hm (Nat.totient_pos.mpr ht0)
  exact hpos.trans_le hdegree

theorem integer_minimal_cyclotomic_complex
    (S : Finset ℕ) (m : ℕ → ℕ) (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ))) :
    (cyclotomicProduct S m).map (Int.castRingHom ℂ) =
      minimalAnnihilator (fun n => (f n : ℂ)) := by
  let fQ : ℕ → ℚ := fun n => f n
  have hfQ : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℚ)) fQ = 0 := by
    rw [hminimal]
    exact minimalAnnihilator_annihilates fQ
  have hb := minimalAnnihilator_map (L := ℂ) fQ
    ((cyclotomicProduct S m).map (Int.castRingHom ℚ))
    ((cyclotomicProduct_monic S m).map _) hfQ
  change (minimalAnnihilator fQ).map (algebraMap ℚ ℂ) =
    minimalAnnihilator (fun n => (fQ n : ℂ)) at hb
  have hmap : ((cyclotomicProduct S m).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      (cyclotomicProduct S m).map (Int.castRingHom ℂ) := by
    ext n
    simp only [coeff_map, Int.coe_castRingHom]
    rfl
  rw [← hminimal] at hb
  rw [hmap] at hb
  simpa only [fQ, Rat.cast_intCast] using hb

/-- The numerator witnesses of a nonzero cyclotomic component have product
norm at least one over the full primitive conjugacy class. -/
theorem minimal_cyclotomic_witness_norm_lower
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    {t : ℕ} (ht : t ∈ S) (hmt : 0 < m t) :
    (1 : ℝ) ≤ ∏ z ∈ primitiveRoots t ℂ,
      ‖(cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) z‖ := by
  let z := @cyclotomicRootValue S
  let d := cyclotomicRootMultiplicity (S := S) m
  have hminC := integer_minimal_cyclotomic_complex S m f hminimal
  have hrecC : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℂ))
      (fun n => (f n : ℂ)) = 0 := by
    rw [hminC]
    exact minimalAnnihilator_annihilates _
  obtain ⟨c, hc⟩ := cyclotomic_recurrence_expansion S m hS (fun n => (f n : ℂ)) hrecC
  have hsplit : linearFactorProduct z d = (cyclotomicProduct S m).map (Int.castRingHom ℂ) :=
    cyclotomicProduct_split S m hS
  have hminimalC : linearFactorProduct z d = minimalAnnihilator (fun n => (f n : ℂ)) :=
    hsplit.trans hminC
  apply primitive_value_norm_product_ge_one t (hS t ht)
  intro w hw
  let i : CyclotomicRootIndex S := ⟨⟨t, ht⟩, ⟨w, hw⟩⟩
  have hdi : 0 < d i := hmt
  have heq := cofactorWitness_eq_top z d (cyclotomicProduct S m)
    (cyclotomicProduct_degree_pos S m ht (hS t ht) hmt) hsplit f c hc i hdi
  change (cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) (z i) ≠ 0
  rw [heq]
  exact filtered_top_ne_zero z d (cyclotomicRootValue_injective S)
    (cyclotomicRootValue_ne_zero S hS) _ hminimalC c hc i hdi

end Erdos345
