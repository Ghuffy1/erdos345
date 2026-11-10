import Erdos345.ChebyshevModulation

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

noncomputable def totalChebyshevMass {I : Type*} [Fintype I] {D : ℕ}
    (c : I → Fin D → ℂ) : ℝ := ∑ i, chebyshevCoefficientMass (c i)

theorem totalChebyshevMass_nonneg {I : Type*} [Fintype I] {D : ℕ}
    (c : I → Fin D → ℂ) : 0 ≤ totalChebyshevMass c :=
  sum_nonneg (fun i _ => chebyshevCoefficientMass_nonneg (c i))

theorem chebyshevMass_le_total {I : Type*} [Fintype I] {D : ℕ}
    (c : I → Fin D → ℂ) (i : I) : chebyshevCoefficientMass (c i) ≤ totalChebyshevMass c :=
  single_le_sum (fun j _ => chebyshevCoefficientMass_nonneg (c j)) (mem_univ i)

theorem totalChebyshevMass_sq_le {I : Type*} [Fintype I] {D : ℕ}
    (c : I → Fin D → ℂ) :
    totalChebyshevMass c ^ 2 ≤ (Fintype.card I : ℝ) * D * ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (I × Fin D))
    (fun _ => (1 : ℝ)) (fun ij => ‖c ij.1 ij.2‖)
  simpa only [one_mul, one_pow, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Fintype.sum_prod_type, Nat.cast_mul,
    totalChebyshevMass, chebyshevCoefficientMass] using h

noncomputable def chebyshevMixingCost (R D : ℕ) (δ : ℝ) : ℝ :=
  4 * R * (D : ℝ) ^ 2 + (R : ℝ) ^ 2 * (1 + 4 * (D : ℝ) ^ 2) * (2 / δ)

/-- Full finite energy estimate for a sum of separated root frequencies,
before converting the coefficient mass to its Euclidean norm. -/
theorem mixedChebyshev_energy_mass_lower {I : Type*} [Fintype I] [DecidableEq I]
    {D : ℕ} (hD : 0 < D) (c : I → Fin D → ℂ) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖conj (z i) * z j - 1‖)
    (L : ℕ) (hL : 0 < L) :
    (L : ℝ) * (Real.pi / (32 * (D : ℝ))) * (∑ i, ∑ j, ‖c i j‖ ^ 2) -
        chebyshevMixingCost (Fintype.card I) D δ * totalChebyshevMass c ^ 2 ≤
      ∑ n ∈ range L, ‖∑ i, chebyshevPhase (z i) (c i) L n‖ ^ 2 := by
  let B := totalChebyshevMass c
  let R := Fintype.card I
  let E := (1 + 4 * (D : ℝ) ^ 2) * B ^ 2 * (2 / δ)
  let v : I → ℕ → ℂ := fun i => chebyshevPhase (z i) (c i) L
  have hB := totalChebyshevMass_nonneg c
  have hBi (i : I) : chebyshevCoefficientMass (c i) ≤ B := chebyshevMass_le_total c i
  have hcross := discrete_sum_energy_ge_diagonal (range L) v E (by dsimp [E]; positivity)
    (fun i j hij => chebyshevPhase_cross_bound (c i) (c j) (z i) (z j) (hz i) (hz j)
      B δ hB (hBi i) (hBi j) hδ (hsep i j hij) L hL)
  have hdiag (i : I) :
      (L : ℝ) * (Real.pi / (32 * (D : ℝ))) * (∑ j, ‖c i j‖ ^ 2) -
        4 * (D : ℝ) ^ 2 * B ^ 2 ≤ ∑ n ∈ range L, ‖v i n‖ ^ 2 := by
    have h := chebyshev_sample_energy_mass_lower hD (c i) L hL
    have hsquare := pow_le_pow_left₀ (chebyshevCoefficientMass_nonneg (c i)) (hBi i) 2
    have hcost := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 4 * (D : ℝ) ^ 2)
    have hv : (∑ n ∈ range L, ‖v i n‖ ^ 2) =
        ∑ n ∈ range L, ‖shiftedChebyshevSeries (c i) ((n : ℝ) / L)‖ ^ 2 := by
      apply sum_congr rfl
      intro n _
      dsimp only [v]
      rw [chebyshevPhase_norm _ (hz i)]
    rw [hv]
    linarith
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ => hdiag i)
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  dsimp only [E, R] at hcross
  change _ ≤ ∑ n ∈ range L, ‖∑ i, v i n‖ ^ 2
  unfold chebyshevMixingCost
  change (L : ℝ) * (Real.pi / (32 * (D : ℝ))) * (∑ i, ∑ j, ‖c i j‖ ^ 2) -
      (4 * (Fintype.card I : ℝ) * (D : ℝ) ^ 2 +
        (Fintype.card I : ℝ) ^ 2 * (1 + 4 * (D : ℝ) ^ 2) * (2 / δ)) * B ^ 2 ≤ _
  nlinarith

theorem mixedChebyshev_energy_lower {I : Type*} [Fintype I] [DecidableEq I]
    {D : ℕ} (hD : 0 < D) (c : I → Fin D → ℂ) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖conj (z i) * z j - 1‖)
    (L : ℕ) (hL : 0 < L) :
    ((L : ℝ) * (Real.pi / (32 * (D : ℝ))) -
        chebyshevMixingCost (Fintype.card I) D δ * (Fintype.card I : ℝ) * D) *
          (∑ i, ∑ j, ‖c i j‖ ^ 2) ≤
      ∑ n ∈ range L, ‖∑ i, chebyshevPhase (z i) (c i) L n‖ ^ 2 := by
  have h := mixedChebyshev_energy_mass_lower hD c z hz δ hδ hsep L hL
  have hcost : 0 ≤ chebyshevMixingCost (Fintype.card I) D δ := by
    unfold chebyshevMixingCost
    positivity
  have hm := mul_le_mul_of_nonneg_left (totalChebyshevMass_sq_le c) hcost
  nlinarith

theorem mixedChebyshev_half_energy_lower {I : Type*} [Fintype I] [DecidableEq I]
    {D : ℕ} (hD : 0 < D) (c : I → Fin D → ℂ) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖conj (z i) * z j - 1‖)
    (L : ℕ) (hL : 0 < L)
    (hbudget : chebyshevMixingCost (Fintype.card I) D δ * (Fintype.card I : ℝ) * D ≤
      (L : ℝ) * (Real.pi / (64 * (D : ℝ)))) :
    (L : ℝ) * (Real.pi / (64 * (D : ℝ))) * (∑ i, ∑ j, ‖c i j‖ ^ 2) ≤
      ∑ n ∈ range L, ‖∑ i, chebyshevPhase (z i) (c i) L n‖ ^ 2 := by
  have h := mixedChebyshev_energy_lower hD c z hz δ hδ hsep L hL
  have hp : Real.pi / (32 * (D : ℝ)) = 2 * (Real.pi / (64 * (D : ℝ))) := by ring
  have hcoef : (L : ℝ) * (Real.pi / (64 * (D : ℝ))) ≤
      (L : ℝ) * (Real.pi / (32 * (D : ℝ))) -
        chebyshevMixingCost (Fintype.card I) D δ * (Fintype.card I : ℝ) * D := by
    rw [hp]
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (sum_nonneg (fun _ _ => sum_nonneg
    (fun _ _ => sq_nonneg _)))).trans h

end Erdos345
