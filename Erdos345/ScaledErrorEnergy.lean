import Erdos345.RationalErrorEnergy

namespace Erdos345

open Finset Polynomial

theorem integer_multiple_minimal_cyclotomic
    (S : Finset ℕ) (m : ℕ → ℕ) (f : ℕ → ℚ) (g : ℕ → ℤ) (q : ℕ) (hq : 0 < q)
    (hscale : ∀ j, (g j : ℚ) = (q : ℚ) * f j)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f) :
    (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun j => (g j : ℚ)) := by
  have hseq : (fun j => (g j : ℚ)) = (q : ℚ) • f := funext hscale
  rw [hseq, minimalAnnihilator_smul f (q : ℚ) (by exact_mod_cast Nat.ne_of_gt hq)]
  exact hminimal

theorem complex_integer_multiple (f : ℕ → ℚ) (g : ℕ → ℤ) (q : ℕ)
    (hscale : ∀ j, (g j : ℚ) = (q : ℚ) * f j) :
    (fun j => (g j : ℂ)) = (q : ℂ) • (fun j => (f j : ℂ)) := by
  funext j
  have h := congrArg (algebraMap ℚ ℂ) (hscale j)
  simpa only [map_mul, map_intCast, map_natCast, eq_ratCast, Pi.smul_apply, smul_eq_mul] using h

theorem rational_error_rootOne_coefficient_height
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (q : ℕ) (hq : 0 < q) (hscale : ∀ j, (g j : ℚ) = (q : ℚ) * f j)
    (m : ℕ → ℕ) (hm : ∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t)
    (hminf : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (a : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (ha : (fun j => (f j : ℂ)) = ∑ ij, a ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (hmt : 0 < m 1) :
    ∃ z : ↥(primitiveRoots 1 ℂ),
      Real.exp (-(Real.log q + 2 * (weightMass N w : ℝ) * Real.log N)) ≤
        ‖primitiveTopCoefficient (Icc 1 N) m a 1 (mem_Icc.mpr ⟨le_refl 1, hN⟩) hmt z‖ := by
  have hming := integer_multiple_minimal_cyclotomic (Icc 1 N) m f g q hq hscale hminf
  have hqC : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
  have hg : (fun j => (g j : ℂ)) = ((q : ℝ) : ℂ) •
      (∑ ij, a ij • exponentialPower (cyclotomicRootValue ij.1) ij.2) := by
    rw [hqC, ← ha]
    exact complex_integer_multiple f g q hscale
  exact exists_large_scaled_rootOne_top_coefficient hw hMass hN m hm g hming a
    (q : ℝ) (by exact_mod_cast hq) hg hmt

theorem rational_error_rootOne_energy_lower
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (q : ℕ) (hq : 0 < q) (hscale : ∀ j, (g j : ℚ) = (q : ℚ) * f j)
    (m : ℕ → ℕ) (hm : ∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t)
    (hminf : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hmt : 0 < m 1) (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(Real.log q + 2 * (weightMass N w : ℝ) * Real.log N)) *
          (L : ℝ) ^ (m 1 - 1) / (4 : ℝ) ^ (m 1 - 1)) ^ 2 ≤
      ∑ j ∈ range L, ‖(f j : ℂ)‖ ^ 2 := by
  have hS : ∀ t ∈ Icc 1 N, 0 < t := fun t ht => (mem_Icc.mp ht).1
  have hcf := rational_minimal_cyclotomic_complex (Icc 1 N) m f hminf
  have hrecf : shiftAction ((cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℂ))
      (fun j => (f j : ℂ)) = 0 := by rw [hcf]; exact minimalAnnihilator_annihilates _
  obtain ⟨a, ha⟩ := cyclotomic_recurrence_expansion (Icc 1 N) m hS (fun j => (f j : ℂ)) hrecf
  obtain ⟨z, hz⟩ := rational_error_rootOne_coefficient_height hw hMass hN f g q hq hscale m hm hminf a ha hmt
  let ht : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_refl 1, hN⟩
  let i : CyclotomicRootIndex (Icc 1 N) := ⟨⟨1, ht⟩, z⟩
  have he := ordinary_cyclotomic_expansion_energy_lower N N L hN hN hL hlarge m
    (flat_multiplicity_le_dimension hw hMass m hm) (fun j => (f j : ℂ)) a ha i hmt
  change (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
      (‖primitiveTopCoefficient (Icc 1 N) m a 1 ht hmt z‖ *
        (L : ℝ) ^ (m 1 - 1) / (4 : ℝ) ^ (m 1 - 1)) ^ 2 ≤ _ at he
  refine le_trans ?_ he
  gcongr

theorem rational_error_rootOne_multiplicity_bound
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (q : ℕ) (hq : 0 < q) (hscale : ∀ j, (g j : ℚ) = (q : ℚ) * f j)
    (m : ℕ → ℕ) (hm : ∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t)
    (hminf : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hmt : 0 < m 1) (L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range L, ‖(f j : ℂ)‖ ^ 2) ≤ E) :
    (m 1 : ℝ) ≤ (Real.log E + 2 * Real.log q + 4 * (weightMass N w : ℝ) * Real.log N -
      Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L := by
  have hLn : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have henergy := (rational_error_rootOne_energy_lower hw hMass hN f g q hq hscale m hm hminf hmt
    L hLn hlarge).trans hE
  have h := multiplicity_bound_of_energy (m 1) hmt (L : ℝ)
    (Real.pi / (64 * (N : ℝ))) (Real.log q + 2 * (weightMass N w : ℝ) * Real.log N)
    E hL (by positivity) henergy
  convert h using 1
  ring

end Erdos345
