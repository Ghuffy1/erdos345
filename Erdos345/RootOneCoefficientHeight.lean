import Erdos345.PrimePowerCoefficientHeight

namespace Erdos345

open Finset Polynomial IsPrimitiveRoot

theorem flat_regularizedNorm_one (N : ℕ) (w : ℕ → ℕ) (hN : 1 ≤ N) :
    regularizedCyclotomicNorm (Icc 1 N) (rootSlots N w) 1 =
      (normalizedMoment N w : ℝ) := by
  have ht : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hz : (1 : ℂ) ∈ primitiveRoots 1 ℂ := by simp [primitiveRoots_one]
  rw [regularizedCyclotomicNorm, primitiveRoots_one, prod_singleton,
    flat_regularizedValue_eq N w 1 ht 1 hz]
  simp only [regularizedPowerProduct, eval_prod, norm_prod, eval_pow, norm_pow]
  trans ∏ i ∈ range N, ((i + 1 : ℕ) : ℝ) ^ w i
  · apply prod_congr rfl
    intro i _
    rw [regularizedPowerFactor_norm_of_dvd 1 (i + 1) zero_lt_one 1
      (IsPrimitiveRoot.one_right_iff.mpr rfl) (one_dvd _)]
  · simp only [normalizedMoment, Nat.cast_prod, Nat.cast_pow]

theorem log_topDenominator_one_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n) :
    Real.log (topDenominator (Icc 1 N) m 1) ≤
      2 * (weightMass N w : ℝ) * Real.log N := by
  let J := weightMass N w
  let b := m 1 - 1
  have ht : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hslot : rootSlots N w 1 ≤ J := by simpa only [one_mul] using rootSlots_mul_le_mass hw 1
  have hb : b ≤ J := (Nat.sub_le _ _).trans ((hm 1 ht).trans hslot)
  have hJF : (J.factorial : ℝ) ≤ (N : ℝ) ^ J := by
    exact_mod_cast (Nat.factorial_le_pow J).trans (Nat.pow_le_pow_left hMass J)
  have hbF : (b.factorial : ℝ) ≤ (N : ℝ) ^ J := by
    have hle : (b.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hb
    exact hle.trans hJF
  have hR : regularizedCyclotomicNorm (Icc 1 N) m 1 ≤ (N : ℝ) ^ J := by
    calc
      _ ≤ regularizedCyclotomicNorm (Icc 1 N) (rootSlots N w) 1 :=
        regularizedCyclotomicNorm_mono _ _ _ hS 1 ht hm
      _ = (normalizedMoment N w : ℝ) := flat_regularizedNorm_one N w hN
      _ ≤ J.factorial := by
        exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos J) (normalizedMoment_dvd_factorial hw)
      _ ≤ (N : ℝ) ^ J := hJF
  have hbpos : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hRpos : 0 < regularizedCyclotomicNorm (Icc 1 N) m 1 :=
    lt_of_lt_of_le zero_lt_one (regularizedCyclotomicNorm_ge_one _ _ hS 1 zero_lt_one)
  have hlogb := Real.log_le_log hbpos hbF
  have hlogR := Real.log_le_log hRpos hR
  rw [Real.log_pow] at hlogb hlogR
  change Real.log ((b.factorial : ℝ) ^ Nat.totient 1 *
    regularizedCyclotomicNorm (Icc 1 N) m 1) ≤ _
  rw [Nat.totient_one, pow_one, Real.log_mul (ne_of_gt hbpos) (ne_of_gt hRpos)]
  change _ ≤ 2 * (J : ℝ) * Real.log N
  linarith

/-- The unscaled integer sequence gives the root-one height budget. Applying
this to an integer multiple of a rational sequence adds the logarithm of
that integer when passing back to the rational coefficient. -/
theorem exists_large_rootOne_top_coefficient
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (hmt : 0 < m 1) :
    ∃ z : ↥(primitiveRoots 1 ℂ),
      Real.exp (-(2 * (weightMass N w : ℝ) * Real.log N)) ≤
        ‖primitiveTopCoefficient (Icc 1 N) m c 1 (mem_Icc.mpr ⟨le_refl 1, hN⟩) hmt z‖ := by
  classical
  let S := Icc 1 N
  have hS : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have ht : 1 ∈ S := mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hcard : Fintype.card ↥(primitiveRoots 1 ℂ) = 1 := by simp [primitiveRoots_one]
  let : Nonempty ↥(primitiveRoots 1 ℂ) := ⟨⟨1, by simp [primitiveRoots_one]⟩⟩
  let g : ↥(primitiveRoots 1 ℂ) → ℝ := fun z => ‖primitiveTopCoefficient S m c 1 ht hmt z‖
  have hg : ∀ z, 0 < g z := fun z => norm_pos_iff.mpr
    (primitiveTopCoefficient_ne_zero S m hS f hminimal c hrep 1 ht hmt z)
  have hprod := minimal_cyclotomic_witness_norm_lower S m hS f hminimal ht hmt
  rw [primitiveTopCoefficient_product_identity S m hS f c hrep 1 ht hmt] at hprod
  have hbudget : Real.log (topDenominator S m 1) ≤
      (Fintype.card ↥(primitiveRoots 1 ℂ) : ℝ) *
        (2 * (weightMass N w : ℝ) * Real.log N) := by
    rw [hcard, Nat.cast_one, one_mul]
    exact log_topDenominator_one_le hw hMass hN m hm
  exact exists_factor_ge_exp_neg g hg (topDenominator S m 1)
    (2 * (weightMass N w : ℝ) * Real.log N)
    (topDenominator_pos S m hS 1 zero_lt_one) hprod hbudget

end Erdos345
