import Erdos345.MixedChebyshevEnergy

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

theorem cyclotomicRootIndex_card_le (N : ℕ) :
    Fintype.card (CyclotomicRootIndex (Icc 1 N)) ≤ N ^ 2 := by
  classical
  change Fintype.card (Σ n : ↥(Icc 1 N), ↥(primitiveRoots (n : ℕ) ℂ)) ≤ N ^ 2
  rw [Fintype.card_sigma]
  have hcard (n : ↥(Icc 1 N)) : Fintype.card ↥(primitiveRoots (n : ℕ) ℂ) =
      (n : ℕ).totient := by
    rw [Fintype.card_coe]
    exact (isPrimitiveRoot_exp (n : ℕ) (Nat.ne_of_gt (mem_Icc.mp n.property).1)).card_primitiveRoots
  simp_rw [hcard]
  calc
    (∑ n : ↥(Icc 1 N), (n : ℕ).totient) ≤ ∑ _n : ↥(Icc 1 N), N := by
      apply sum_le_sum
      intro n _
      exact (Nat.totient_le n).trans (mem_Icc.mp n.property).2
    _ = N ^ 2 := by simp [Nat.card_Icc, pow_two]

theorem chebyshevMixingCost_polynomial_bound (R D N : ℕ)
    (hD : 0 < D) (hN : 0 < N) (hR : R ≤ N ^ 2) :
    chebyshevMixingCost R D (1 / (N : ℝ) ^ 2) * (R : ℝ) * D ≤
      16 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hRR : (R : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hR
  have hN4 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hNR (by omega)
  have hD3 : (D : ℝ) ≤ (D : ℝ) ^ 3 := le_self_pow₀ hDR (by omega)
  calc
    _ = 4 * (R : ℝ) ^ 2 * (D : ℝ) ^ 3 +
        2 * (R : ℝ) ^ 3 * (N : ℝ) ^ 2 * D +
        8 * (R : ℝ) ^ 3 * (N : ℝ) ^ 2 * (D : ℝ) ^ 3 := by
      unfold chebyshevMixingCost
      field_simp
      ring
    _ ≤ 4 * ((N : ℝ) ^ 2) ^ 2 * (D : ℝ) ^ 3 +
        2 * ((N : ℝ) ^ 2) ^ 3 * (N : ℝ) ^ 2 * D +
        8 * ((N : ℝ) ^ 2) ^ 3 * (N : ℝ) ^ 2 * (D : ℝ) ^ 3 := by gcongr
    _ = 4 * (N : ℝ) ^ 4 * (D : ℝ) ^ 3 +
        2 * (N : ℝ) ^ 8 * D + 8 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 := by ring
    _ ≤ 4 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 +
        2 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 + 8 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 := by gcongr
    _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ (N : ℝ) ^ 8 * (D : ℝ) ^ 3 by positivity]

/-- The interval requirement is a polynomial in the maximum root order
and the common polynomial dimension. No exponential separation cost occurs. -/
theorem cyclotomicChebyshev_energy_lower (N D L : ℕ) (hN : 0 < N) (hD : 0 < D) (hL : 0 < L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (D : ℝ) ^ 4 ≤ Real.pi * L)
    (c : CyclotomicRootIndex (Icc 1 N) → Fin D → ℂ) :
    (L : ℝ) * (Real.pi / (64 * (D : ℝ))) * (∑ i, ∑ j, ‖c i j‖ ^ 2) ≤
      ∑ n ∈ range L, ‖∑ i, chebyshevPhase (cyclotomicRootValue i) (c i) L n‖ ^ 2 := by
  classical
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply mixedChebyshev_half_energy_lower hD c (@cyclotomicRootValue (Icc 1 N))
    (fun i => ((isPrimitiveRoot_of_mem_primitiveRoots i.2.property).isOfFinOrder
      (Nat.ne_of_gt (mem_Icc.mp i.1.property).1)).norm_eq_one)
    (1 / (N : ℝ) ^ 2) (by positivity)
    (fun i j hij => cyclotomic_root_separation N i j hij) L hL
  have hcost := chebyshevMixingCost_polynomial_bound
    (Fintype.card (CyclotomicRootIndex (Icc 1 N))) D N hD hN (cyclotomicRootIndex_card_le N)
  have hbudget : 16 * (N : ℝ) ^ 8 * (D : ℝ) ^ 3 ≤
      (L : ℝ) * (Real.pi / (64 * (D : ℝ))) := by
    have heq : (L : ℝ) * (Real.pi / (64 * (D : ℝ))) =
        ((L : ℝ) * Real.pi) / (64 * (D : ℝ)) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 64 * (D : ℝ))).mpr
    nlinarith [hlarge]
  exact hcost.trans hbudget

end Erdos345
