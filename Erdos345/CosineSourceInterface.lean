import Erdos345.CosineFlatCoefficientNorm
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Erdos345

open Finset

theorem flatCosineNonnegative_of_real (N : ℕ) (w : ℕ → ℕ) (a : ℝ)
    (hcos : ∀ θ : ℝ, 0 ≤ a + ∑ i ∈ range N,
      (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) :
    flatCosineNonnegative N w a := by
  intro z hz
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  have heq : (∑ i ∈ range N, (w i : ℝ) *
      (Complex.exp ((θ : ℂ) * Complex.I) ^ (i + 1)).re) =
      ∑ i ∈ range N, (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
    apply sum_congr rfl
    intro i _
    rw [← Complex.exp_nat_mul]
    have harg : ((i + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) =
        ((((i + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  rw [heq]
  exact hcos θ

/-- This theorem converts the precise real-cosine existence input into the
flat coefficient family. The existence input is an explicit premise: the
published Belov--Konyagin result is not imported as a Lean axiom. -/
theorem flat_family_from_cosine_existence
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ range J, (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5)
    (k : ℕ) (hk : 0 < k) :
    ∀ d : ℕ, 0 < d → d ≤ k → ∃ w : ℕ → ℕ,
      AntitoneOn w (Set.Iio (d + 1)) ∧ weightMass (d + 1) w = d + 1 ∧
        coefficientL1 (flatPolynomial (d + 1) w) ≤ Real.exp (flatNormConstant * logScale k ^ 6) := by
  intro d _hd hdk
  obtain ⟨w, a, hw, hmass, hcos, ha⟩ := hinput (d + 1) (Nat.succ_pos _)
  exact ⟨w, hw, hmass, flat_coefficient_norm_below_degree k (d + 1) hk (Nat.succ_pos _)
    (Nat.succ_le_succ hdk) w a hmass (flatCosineNonnegative_of_real (d + 1) w a hcos) ha⟩

theorem exists_good_center_bound_from_cosine_existence
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ range J, (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5)
    (Y : ℕ) (hY : 0 < Y) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧ ∀ q u : ℕ,
      1 < q → u.Coprime q → q ∣ k.factorial * (k + 1).factorial →
        (k : ℝ) ^ 2 < centerEnergy k u q (quasipolynomialCenterPrefix k flatNormConstant) := by
  obtain ⟨k, hkY, hk2Y, hcenter⟩ :=
    exists_good_quasipolynomial_center_bound Y hY flatNormConstant flatNormConstant_nonneg
  refine ⟨k, hkY, hk2Y, ?_⟩
  exact hcenter (flat_family_from_cosine_existence hinput k (hY.trans_le hkY))

end Erdos345
