import Erdos345.FlatErrorRecurrence

namespace Erdos345

open Finset Polynomial

theorem translated_phase_identity (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ)) (a j : ℕ) :
    f (a + j) + (g (a + j) : ℚ) = (P.comp (X + C (a : ℚ))).eval (j : ℚ) := by
  simpa only [eval_comp, eval_add, eval_X, eval_C, Nat.cast_add, add_comm] using hphase (a + j)

theorem translated_flat_recurrence (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ)
    (hg : shiftAction (flatPolynomial N w) g = 0) (a : ℕ) :
    shiftAction (flatPolynomial N w) (fun j => g (a + j)) = 0 := by
  funext j
  rw [shiftAction_translate_general]
  exact congrFun hg (a + j)

theorem exists_integer_error_multiple (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ)) (q : ℕ)
    (hInt : integerValuedPolynomial (C (q : ℚ) * P)) :
    ∃ z : ℕ → ℤ, ∀ j, (z j : ℚ) = (q : ℚ) * f j := by
  have hint (j : ℕ) : ∃ z : ℤ, (q : ℚ) * P.eval (j : ℚ) = (z : ℚ) := by
    simpa only [eval_mul, eval_C, Int.cast_natCast] using hInt (j : ℤ)
  choose A hA using hint
  refine ⟨fun j => A j - (q : ℤ) * g j, ?_⟩
  intro j
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [← hA j, ← hphase j]
  ring

/-- The height packet is measured on the actual translated interval, but
its cyclotomic multiplicities are those of the original error sequence. -/
theorem exists_flat_error_window_multiplicity_bounds
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X])
    (hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ))
    (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0)
    (q : ℕ) (hq : 0 < q) (hqf : ∀ j, (z j : ℚ) = (q : ℚ) * f j)
    (a L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range L, ‖(f (a + j) : ℂ)‖ ^ 2) ≤ E) :
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
  have hdeg' : (P.comp (X + C (a : ℚ))).natDegree < weightMass N w := by
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hdeg
  obtain ⟨m, hm, hmin, hp, hroot⟩ := exists_flat_error_multiplicity_bounds hw hMass
    (fun j => f (a + j)) (fun j => g (a + j)) (fun j => z (a + j))
    (P.comp (X + C (a : ℚ))) (translated_phase_identity f g P hphase a) hdeg'
    (translated_flat_recurrence N w g hg a) q hq (fun j => hqf (a + j)) L hL hlarge E hE
  refine ⟨m, hm, ?_, hp, hroot⟩
  exact hmin.trans (minimalAnnihilator_flat_translate w f (flat_error_annihilation N w f g P hphase hdeg hg) a)

/-- The rational-phase interface used by the conductor argument: the
integer multiple is constructed from integer-valuedness of q*P. -/
theorem exists_rational_phase_height_bounds
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (g : ℕ → ℤ) (P : ℚ[X]) (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0)
    (q : ℕ) (hq : 0 < q) (hInt : integerValuedPolynomial (C (q : ℚ) * P))
    (a L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ j ∈ range L, ‖((P.eval ((a + j : ℕ) : ℚ) - (g (a + j) : ℚ) : ℚ) : ℂ)‖ ^ 2) ≤ E) :
    ∃ m : ℕ → ℕ,
      (∀ t ∈ Icc 1 N, m t ≤ rootSlots N w t) ∧
      (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
        minimalAnnihilator (fun j : ℕ => P.eval (j : ℚ) - (g j : ℚ)) ∧
      (∀ p k : ℕ, p.Prime → p ^ (k + 1) ∈ Icc 1 N → 0 < m (p ^ (k + 1)) →
        (m (p ^ (k + 1)) : ℝ) ≤
          (Real.log E + 8 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N -
            Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) ∧
      (0 < m 1 → (m 1 : ℝ) ≤
        (Real.log E + 2 * Real.log q + 4 * (weightMass N w : ℝ) * Real.log N -
          Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) := by
  let f : ℕ → ℚ := fun j => P.eval (j : ℚ) - (g j : ℚ)
  have hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ) := by intro j; simp only [f, sub_add_cancel]
  obtain ⟨z, hz⟩ := exists_integer_error_multiple f g P hphase q hInt
  exact exists_flat_error_window_multiplicity_bounds hw hMass f g z P hphase hdeg hg q hq hz
    a L hL hlarge E hE

end Erdos345
