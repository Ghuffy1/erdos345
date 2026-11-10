import Erdos345.RationalErrorHeight

namespace Erdos345

open Finset Polynomial

theorem rational_error_primePower_energy_lower
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
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1)))
    (L : ℕ) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L) :
    (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
        (Real.exp (-(4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)) *
          (L : ℝ) ^ (m (p ^ (k + 1)) - 1) / (4 : ℝ) ^ (m (p ^ (k + 1)) - 1)) ^ 2 ≤
      ∑ j ∈ range L, ‖(f j : ℂ)‖ ^ 2 := by
  have hS : ∀ t ∈ Icc 1 N, 0 < t := fun t ht => (mem_Icc.mp ht).1
  have hcf := rational_minimal_cyclotomic_complex (Icc 1 N) m f hminf
  have hrecf : shiftAction ((cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℂ))
      (fun j => (f j : ℂ)) = 0 := by rw [hcf]; exact minimalAnnihilator_annihilates _
  obtain ⟨a, ha⟩ := cyclotomic_recurrence_expansion (Icc 1 N) m hS (fun j => (f j : ℂ)) hrecf
  obtain ⟨z, hz⟩ := rational_error_primePower_coefficient_height hw hMass f g P hphase hdeg
    m n hm hn hminf hming a ha p k hp ht hmt
  let i : CyclotomicRootIndex (Icc 1 N) := ⟨⟨p ^ (k + 1), ht⟩, z⟩
  have hN : 0 < N := (pow_pos hp.pos (k + 1)).trans_le (mem_Icc.mp ht).2
  have he := ordinary_cyclotomic_expansion_energy_lower N N L hN hN hL hlarge m
    (flat_multiplicity_le_dimension hw hMass m hm) (fun j => (f j : ℂ)) a ha i hmt
  change (L : ℝ) * (Real.pi / (64 * (N : ℝ))) *
      (‖primitiveTopCoefficient (Icc 1 N) m a (p ^ (k + 1)) ht hmt z‖ *
        (L : ℝ) ^ (m (p ^ (k + 1)) - 1) / (4 : ℝ) ^ (m (p ^ (k + 1)) - 1)) ^ 2 ≤ _ at he
  refine le_trans ?_ he
  gcongr

theorem rational_error_primePower_multiplicity_bound
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
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1)))
    (L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range L, ‖(f j : ℂ)‖ ^ 2) ≤ E) :
    (m (p ^ (k + 1)) : ℝ) ≤
      (Real.log E + 8 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N -
        Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L := by
  have hLn : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hN : 0 < N := (pow_pos hp.pos (k + 1)).trans_le (mem_Icc.mp ht).2
  have henergy := (rational_error_primePower_energy_lower hw hMass f g P hphase hdeg
    m n hm hn hminf hming p k hp ht hmt L hLn hlarge).trans hE
  have h := multiplicity_bound_of_energy (m (p ^ (k + 1))) hmt (L : ℝ)
    (Real.pi / (64 * (N : ℝ))) (4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)
    E hL (by positivity) henergy
  convert h using 1
  ring

end Erdos345
