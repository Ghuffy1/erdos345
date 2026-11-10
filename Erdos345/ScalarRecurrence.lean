import Erdos345.RootOneCoefficientHeight

namespace Erdos345

open Finset Polynomial

theorem sequenceAnnihilator_smul {K : Type*} [Field K]
    (f : ℕ → K) (a : K) (ha : a ≠ 0) :
    sequenceAnnihilator (a • f) = sequenceAnnihilator f := by
  ext p
  change shiftAction p (a • f) = 0 ↔ shiftAction p f = 0
  rw [map_smul, smul_eq_zero, or_iff_right ha]

theorem minimalAnnihilator_smul {K : Type*} [Field K]
    (f : ℕ → K) (a : K) (ha : a ≠ 0) :
    minimalAnnihilator (a • f) = minimalAnnihilator f := by
  classical
  exact congrArg (fun I : Ideal K[X] => normalize (Submodule.IsPrincipal.generator I))
    (sequenceAnnihilator_smul f a ha)

theorem scale_finite_expansion {I : Type*} [Fintype I]
    (v : I → ℕ → ℂ) (c : I → ℂ) (a : ℂ) :
    a • (∑ i, c i • v i) = ∑ i, (a * c i) • v i := by
  simp only [Finset.smul_sum, smul_smul]

theorem primitiveTopCoefficient_scale
    (S : Finset ℕ) (m : ℕ → ℕ)
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (a : ℂ) (t : ℕ) (ht : t ∈ S) (hmt : 0 < m t) (z : ↥(primitiveRoots t ℂ)) :
    primitiveTopCoefficient S m (fun i => a * c i) t ht hmt z =
      a * primitiveTopCoefficient S m c t ht hmt z := rfl

theorem norm_ge_exp_of_scaled (q B : ℝ) (hq : 0 < q) (a : ℂ)
    (h : Real.exp (-B) ≤ ‖(q : ℂ) * a‖) :
    Real.exp (-(Real.log q + B)) ≤ ‖a‖ := by
  have heq : Real.exp (-(Real.log q + B)) = Real.exp (-B) / q := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hq]
    ring
  rw [heq]
  apply (div_le_iff₀ hq).mpr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at h
  nlinarith

/-- Passing from an integral multiple back to the original coefficients
has exactly the log(q) cost retained in the root-one height argument. -/
theorem exists_large_scaled_rootOne_top_coefficient
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (q : ℝ) (hq : 0 < q)
    (hrep : (fun n => (f n : ℂ)) = (q : ℂ) •
      (∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2))
    (hmt : 0 < m 1) :
    ∃ z : ↥(primitiveRoots 1 ℂ),
      Real.exp (-(Real.log q + 2 * (weightMass N w : ℝ) * Real.log N)) ≤
        ‖primitiveTopCoefficient (Icc 1 N) m c 1 (mem_Icc.mpr ⟨le_refl 1, hN⟩) hmt z‖ := by
  have hrep' : (fun n => (f n : ℂ)) = ∑ ij, ((q : ℂ) * c ij) •
      exponentialPower (cyclotomicRootValue ij.1) ij.2 := by
    rw [hrep, scale_finite_expansion]
  obtain ⟨z, hz⟩ := exists_large_rootOne_top_coefficient hw hMass hN m hm f hminimal
    (fun ij => (q : ℂ) * c ij) hrep' hmt
  refine ⟨z, ?_⟩
  rw [primitiveTopCoefficient_scale] at hz
  exact norm_ge_exp_of_scaled q (2 * (weightMass N w : ℝ) * Real.log N) hq _ hz

end Erdos345
