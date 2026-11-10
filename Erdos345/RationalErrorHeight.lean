import Erdos345.PolynomialPerturbation

namespace Erdos345

open Finset Polynomial

theorem top_norm_eq_of_component_sum (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : m = n) (a : Fin m → ℂ) (b : Fin n → ℂ)
    (hsum : ∀ j : ℕ, ∀ hjm : j < m, ∀ hjn : j < n, a ⟨j, hjm⟩ + b ⟨j, hjn⟩ = 0) :
    ‖a ⟨m - 1, by omega⟩‖ = ‖b ⟨n - 1, by omega⟩‖ := by
  subst n
  have h := hsum (m - 1) (by omega) (by omega)
  rw [eq_neg_of_add_eq_zero_left h, norm_neg]

/-- The nontrivial coefficient height of a rational error comes from the
integer sequence subtracted from the polynomial phase. No factor q is
introduced into this prime-power bound. -/
theorem rational_error_primePower_coefficient_height
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ))
    (hdeg : P.degree < weightMass N w)
    (m n : ℕ → ℕ)
    (hm : ∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t)
    (hn : ∀ t ∈ Icc 1 N, n t ≤ rootSlots N w t)
    (hminf : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hming : (cyclotomicProduct (Icc 1 N) n).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun j => (g j : ℚ)))
    (a : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (ha : (fun j => (f j : ℂ)) = ∑ ij, a ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1))) :
    ∃ z : ↥(primitiveRoots (p ^ (k + 1)) ℂ),
      Real.exp (-(4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)) ≤
        ‖primitiveTopCoefficient (Icc 1 N) m a (p ^ (k + 1)) ht hmt z‖ := by
  classical
  let S := Icc 1 N
  have hS : ∀ t ∈ S, 0 < t := fun t ht => (mem_Icc.mp ht).1
  have htpos : 0 < p ^ (k + 1) := pow_pos hp.pos _
  have ht1 : p ^ (k + 1) ≠ 1 := ne_of_gt (one_lt_pow₀ hp.one_lt (by omega : k + 1 ≠ 0))
  have hN : 0 < N := htpos.trans_le (mem_Icc.mp ht).2
  have h1 : 1 ∈ S := mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hcg := integer_minimal_cyclotomic_complex S n g hming
  have hrecg : shiftAction ((cyclotomicProduct S n).map (Int.castRingHom ℂ))
      (fun j => (g j : ℂ)) = 0 := by rw [hcg]; exact minimalAnnihilator_annihilates _
  obtain ⟨b, hb⟩ := cyclotomic_recurrence_expansion S n hS (fun j => (g j : ℂ)) hrecg
  have hb' : (fun j => ((g j : ℚ) : ℂ)) =
      ∑ ij, b ij • exponentialPower (cyclotomicRootValue ij.1) ij.2 := by
    simpa only [Rat.cast_intCast] using hb
  have hP : (P.map (algebraMap ℚ ℂ)).degree < rootSlots N w 1 := by
    rw [rootSlots_one]
    exact degree_map_le.trans_lt hdeg
  have hphaseC : (fun j => (f j : ℂ)) + (fun j => ((g j : ℚ) : ℂ)) =
      fun j : ℕ => (P.map (algebraMap ℚ ℂ)).eval (j : ℂ) := by
    simpa only [Rat.cast_intCast] using complex_polynomial_sum_of_rational f g P hphase
  have hcompare := rational_polynomial_perturbation_components S hS h1 m n (rootSlots N w)
    hm hn f (fun j => (g j : ℚ)) hminf hming a b ha hb' (P.map (algebraMap ℚ ℂ)) hP hphaseC
  have hmn : m (p ^ (k + 1)) = n (p ^ (k + 1)) := hcompare.1 _ ht ht1
  have hnt : 0 < n (p ^ (k + 1)) := by omega
  obtain ⟨z, hz⟩ := exists_large_primePower_top_coefficient hw hMass n hn g hming b hb p k hp ht hnt
  let i : CyclotomicRootIndex S := ⟨⟨p ^ (k + 1), ht⟩, z⟩
  have hnorm := top_norm_eq_of_component_sum _ _ hmt hnt hmn
    (fun j => a ⟨i, j⟩) (fun j => b ⟨i, j⟩)
    (fun j hjm hjn => hcompare.2 i ht1 j hjm hjn)
  change ‖primitiveTopCoefficient S m a (p ^ (k + 1)) ht hmt z‖ =
    ‖primitiveTopCoefficient S n b (p ^ (k + 1)) ht hnt z‖ at hnorm
  exact ⟨z, hz.trans_eq hnorm.symm⟩

end Erdos345
