import Erdos345.ScaledErrorEnergy

namespace Erdos345

open Finset Polynomial

theorem rational_cast_flat_recurrence (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ)
    (hg : shiftAction (flatPolynomial N w) g = 0) :
    shiftAction ((flatPolynomial N w).map (Int.castRingHom ℚ)) (fun j => (g j : ℚ)) = 0 := by
  funext j
  change shiftAction ((flatPolynomial N w).map (Int.castRingHom ℚ))
    (fun k => (Int.castRingHom ℚ) (g k)) j = 0
  rw [shiftAction_map, congrFun hg j]
  rfl

theorem flat_error_annihilation (N : ℕ) (w : ℕ → ℕ) (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ))
    (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0) :
    shiftAction ((flatPolynomial N w).map (Int.castRingHom ℚ)) f = 0 := by
  have hfg : f = (fun j : ℕ => P.eval (j : ℚ)) - (fun j => (g j : ℚ)) := by
    funext j
    exact eq_sub_of_add_eq (hphase j)
  rw [hfg, map_sub, flatPolynomial_annihilates N w P hdeg,
    rational_cast_flat_recurrence N w g hg, sub_self]

theorem exists_flat_error_minimal_pair (N : ℕ) (w : ℕ → ℕ)
    (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ))
    (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0) :
    ∃ m n : ℕ → ℕ,
      (∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t) ∧
      (∀ t ∈ Icc 1 N, n t ≤ rootSlots N w t) ∧
      (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f ∧
      (cyclotomicProduct (Icc 1 N) n).map (Int.castRingHom ℚ) =
        minimalAnnihilator (fun j => (g j : ℚ)) := by
  obtain ⟨m, hm, hmf⟩ := exists_minimal_flat_cyclotomic_annihilator N w f
    (flat_error_annihilation N w f g P hphase hdeg hg)
  obtain ⟨n, hn, hng⟩ := exists_minimal_flat_cyclotomic_annihilator N w (fun j => (g j : ℚ))
    (rational_cast_flat_recurrence N w g hg)
  exact ⟨m, n, hm, hn, hmf, hng⟩

/-- Simultaneous bounds for every retained prime-power component and the
root-one component of the actual rational error's minimal recurrence. -/
theorem exists_flat_error_multiplicity_bounds
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ))
    (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0)
    (q : ℕ) (hq : 0 < q) (hqf : ∀ j, (z j : ℚ) = (q : ℚ) * f j)
    (L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range L, ‖(f j : ℂ)‖ ^ 2) ≤ E) :
    ∃ m : ℕ → ℕ,
      (∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t) ∧
      (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) = minimalAnnihilator f ∧
      (∀ p k : ℕ, p.Prime → p ^ (k + 1) ∈ Icc 1 N → 0 < m (p ^ (k + 1)) →
        (m (p ^ (k + 1)) : ℝ) ≤
          (Real.log E + 8 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N -
            Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) ∧
      (0 < m 1 → (m 1 : ℝ) ≤
        (Real.log E + 2 * Real.log q + 4 * (weightMass N w : ℝ) * Real.log N -
          Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) := by
  obtain ⟨m, n, hm, hn, hmf, hng⟩ := exists_flat_error_minimal_pair N w f g P hphase hdeg hg
  have hP : P.degree < weightMass N w := degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hdeg)
  have hN : 1 ≤ N := (Nat.succ_le_of_lt (Nat.zero_le P.natDegree |>.trans_lt hdeg)).trans hMass
  refine ⟨m, hm, hmf, ?_, ?_⟩
  · intro p k hp ht hmt
    exact rational_error_primePower_multiplicity_bound hw hMass f g P hphase hP
      m n hm hn hmf hng p k hp ht hmt L hL hlarge E hE
  · intro hmt
    exact rational_error_rootOne_multiplicity_bound hw hMass hN f z q hq hqf m hm hmf hmt
      L hL hlarge E hE

end Erdos345
