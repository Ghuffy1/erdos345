import Erdos345.OneStepReduction

namespace Erdos345

open Finset Polynomial

theorem power_modulus_one_of_small_heights (S : Finset ℕ) (m : ℕ → ℕ)
    (q k : ℕ) (h1 : 1 ∈ S)
    (hglobal : ∀ n, (q : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n)
    (T : ℝ) (hT : T < 1) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ p : ℕ, p.Prime →
      ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T) : q = 1 := by
  have hm0 : m 1 = 0 := by
    by_contra hm
    have hpos : (1 : ℝ) ≤ m 1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    linarith
  apply Nat.dvd_one.mp
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 1 q).mpr
  intro p e hp hpeq
  have hdiv : ((p ^ e : ℕ) : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpeq
  have hpT : T < (p : ℝ) := hT.trans (by exact_mod_cast hp.one_lt)
  have h := (large_prime_power_reduction S m p e k hp h1 T hpT (hbound p hp)
    (fun n => hdiv.trans (hglobal n))).1 hm0
  rw [h]

/-- A window-height budget below one forces the original denominator to
be one. No limiting or prime-distribution assertion is used. -/
theorem rational_phase_window_modulus_one
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hN : 1 ≤ N) (hMass : weightMass N w ≤ N)
    (g : ℕ → ℤ) (P : ℚ[X]) (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0)
    (q u k : ℕ) (hq : 0 < q) (hu : u.Coprime q)
    (hInt : integerValuedPolynomial (C (q : ℚ) * P))
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (a L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ)
    (hE : (∑ j ∈ range L,
      ‖((P.eval ((a + j : ℕ) : ℚ) - (g (a + j) : ℚ) : ℚ) : ℂ)‖ ^ 2) ≤ E)
    (hsmall : windowHeightBudget N (weightMass N w) q L E < 1) : q = 1 := by
  let f : ℕ → ℚ := fun j => P.eval (j : ℚ) - (g j : ℚ)
  have hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ) := by
    intro j
    simp only [f, sub_add_cancel]
  obtain ⟨m, _hm, hmin, hprime, hroot⟩ := exists_rational_phase_height_bounds
    hw hMass g P hdeg hg q hq hInt a L hL hlarge E hE
  have hheight := height_bounds_to_uniform N (weightMass N w) q L m hL E hprime hroot
  obtain ⟨z, hz⟩ := exists_integer_error_multiple f g P hphase q hInt
  exact power_modulus_one_of_small_heights (Icc 1 N) m q k (mem_Icc.mpr ⟨le_rfl, hN⟩)
    (rational_error_annihilator_mod_power (Icc 1 N) m f g z P q u k hq hu hmin hphase hz hPmod)
    (windowHeightBudget N (weightMass N w) q L E) hsmall hheight.1 hheight.2

theorem exact_reduction_step_modulus_one (q u k d X W : ℕ)
    (hq : 0 < q) (hu : u.Coprime q) (hred : q ∣ reductionModulus k d)
    (w : ℕ → ℕ) (hw : AntitoneOn w (Set.Iio (d + 1)))
    (hmass : weightMass (d + 1) w = d + 1)
    (B E : ℝ) (hB : coefficientL1 (flatPolynomial (d + 1) w) ≤ B)
    (hcenter : centerEnergy k u q X ≤ E)
    (hsize : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((d + 1 : ℕ) : ℝ) ^ 2 ≤ X)
    (hW : (16 : ℝ) ≤ W)
    (hlarge : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsmall : windowHeightBudget (d + 1) (d + 1) q W (E / 4) < 1) : q = 1 := by
  obtain ⟨P, hdegree, hInt, hmod⟩ := exists_rational_reduction_phase q u k d hq hred
  have hdeg : P.natDegree < weightMass (d + 1) w := by omega
  have hmodNat : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k := by
    intro n
    simpa only [Int.cast_natCast] using hmod (n : ℤ)
  have hsize' : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) +
      ((d + 1 : ℕ) : ℝ) * weightMass (d + 1) w ≤ X := by
    rw [hmass]
    simpa only [pow_two] using hsize
  obtain ⟨a, L, g, hWL, _ha, hg, henergy⟩ := exists_reduced_phase_long_window
    (d + 1) w P hdeg q u k X W hq hmodNat B E hB hcenter hsize'
  have hLR : (W : ℝ) ≤ L := by exact_mod_cast hWL
  have hL : (16 : ℝ) ≤ L := hW.trans hLR
  have hlargeL : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L :=
    hlarge.trans (mul_le_mul_of_nonneg_left hLR Real.pi_pos.le)
  have hT := windowHeightBudget_antitone_length (d + 1) (d + 1) q W L (by omega) hq hW hWL (E / 4)
  apply rational_phase_window_modulus_one hw (by omega) hmass.le g P hdeg hg q u k hq hu
    hInt hmodNat a L hL hlargeL (E / 4) henergy
  rw [hmass]
  exact hT.trans_lt hsmall

end Erdos345
