import Erdos345.OrdinaryRecurrenceEnergy
import Erdos345.ScalarRecurrence

namespace Erdos345

open Finset Polynomial

theorem flat_multiplicity_le_dimension {N : ℕ} {w : ℕ → ℕ}
    (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n) :
    ∀ n ∈ Icc 1 N, m n ≤ N := by
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hslots := rootSlots_mul_le_mass hw n
  have hbound := hm n hn
  nlinarith

/-- Quantitative energy of an integer cyclotomic recurrence at a retained
prime-power component. The conjugate norm argument and the interval Gram
argument are both discharged, with their explicit hypotheses retained. -/
theorem integer_recurrence_primePower_energy_lower
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) = ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1)))
    (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)) *
          (L : ℝ) ^ (m (p ^ (k + 1)) - 1) / (4 : ℝ) ^ (m (p ^ (k + 1)) - 1)) ^ 2 ≤
      ∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2 := by
  obtain ⟨z, hz⟩ := exists_large_primePower_top_coefficient hw hMass m hm f hminimal c hrep p k hp ht hmt
  let i : CyclotomicRootIndex (Icc 1 N) := ⟨⟨p ^ (k + 1), ht⟩, z⟩
  have hN : 0 < N := (pow_pos hp.pos (k + 1)).trans_le (mem_Icc.mp ht).2
  have he := ordinary_cyclotomic_expansion_energy_lower N N L hN hN hL hlarge m
    (flat_multiplicity_le_dimension hw hMass m hm) (fun n => (f n : ℂ)) c hrep i hmt
  change (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
      (‖primitiveTopCoefficient (Icc 1 N) m c (p ^ (k + 1)) ht hmt z‖ *
        (L : ℝ) ^ (m (p ^ (k + 1)) - 1) / (4 : ℝ) ^ (m (p ^ (k + 1)) - 1)) ^ 2 ≤ _ at he
  refine le_trans ?_ he
  gcongr

theorem integer_recurrence_rootOne_energy_lower
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) = ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (hmt : 0 < m 1) (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(2 * (weightMass N w : ℝ) * Real.log N)) *
          (L : ℝ) ^ (m 1 - 1) / (4 : ℝ) ^ (m 1 - 1)) ^ 2 ≤
      ∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2 := by
  obtain ⟨z, hz⟩ := exists_large_rootOne_top_coefficient hw hMass hN m hm f hminimal c hrep hmt
  let ht : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_refl 1, hN⟩
  let i : CyclotomicRootIndex (Icc 1 N) := ⟨⟨1, ht⟩, z⟩
  have he := ordinary_cyclotomic_expansion_energy_lower N N L hN hN hL hlarge m
    (flat_multiplicity_le_dimension hw hMass m hm) (fun n => (f n : ℂ)) c hrep i hmt
  change (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
      (‖primitiveTopCoefficient (Icc 1 N) m c 1 ht hmt z‖ *
        (L : ℝ) ^ (m 1 - 1) / (4 : ℝ) ^ (m 1 - 1)) ^ 2 ≤ _ at he
  refine le_trans ?_ he
  gcongr

theorem minimal_integer_primePower_energy_lower
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1)))
    (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)) *
          (L : ℝ) ^ (m (p ^ (k + 1)) - 1) / (4 : ℝ) ^ (m (p ^ (k + 1)) - 1)) ^ 2 ≤
      ∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2 := by
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hc := integer_minimal_cyclotomic_complex (Icc 1 N) m f hminimal
  have hrec : shiftAction ((cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℂ))
      (fun n => (f n : ℂ)) = 0 := by
    rw [hc]
    exact minimalAnnihilator_annihilates _
  obtain ⟨c, hrep⟩ := cyclotomic_recurrence_expansion (Icc 1 N) m hS (fun n => (f n : ℂ)) hrec
  exact integer_recurrence_primePower_energy_lower hw hMass m hm f hminimal c hrep p k hp ht hmt L hL hlarge

theorem minimal_integer_rootOne_energy_lower
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (hmt : 0 < m 1) (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(2 * (weightMass N w : ℝ) * Real.log N)) *
          (L : ℝ) ^ (m 1 - 1) / (4 : ℝ) ^ (m 1 - 1)) ^ 2 ≤
      ∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2 := by
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hc := integer_minimal_cyclotomic_complex (Icc 1 N) m f hminimal
  have hrec : shiftAction ((cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℂ))
      (fun n => (f n : ℂ)) = 0 := by
    rw [hc]
    exact minimalAnnihilator_annihilates _
  obtain ⟨c, hrep⟩ := cyclotomic_recurrence_expansion (Icc 1 N) m hS (fun n => (f n : ℂ)) hrec
  exact integer_recurrence_rootOne_energy_lower hw hMass hN m hm f hminimal c hrep hmt L hL hlarge

end Erdos345
