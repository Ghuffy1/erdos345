import Erdos345.RegularizedPowerProduct
import Mathlib.Tactic.GCongr

namespace Erdos345

open Finset Polynomial

theorem flat_regularizedValue_eq (N : ℕ) (w : ℕ → ℕ) (t : ℕ)
    (ht : t ∈ Icc 1 N) (z : ℂ) (hz : z ∈ primitiveRoots t ℂ) :
    regularizedCyclotomicValue (Icc 1 N) (rootSlots N w) t z =
      (regularizedPowerProduct N w t z).eval z := by
  let i : CyclotomicRootIndex (Icc 1 N) := ⟨⟨t, ht⟩, ⟨z, hz⟩⟩
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hfactor : linearFactorProduct (@cyclotomicRootValue (Icc 1 N))
      (cyclotomicRootMultiplicity (rootSlots N w)) =
      (X - C z) ^ rootSlots N w t * regularizedPowerProduct N w t z := by
    rw [cyclotomicProduct_split _ _ hS, ← rawFlatPolynomial_eq_cyclotomic]
    exact (regularizedPowerProduct_factor N w t z (isPrimitiveRoot_of_mem_primitiveRoots hz)).symm
  have hcomp := complementFactor_of_factorization (@cyclotomicRootValue (Icc 1 N))
    (cyclotomicRootMultiplicity (rootSlots N w)) i 1 (regularizedPowerProduct N w t z)
    (X - C z) (by simp [i, cyclotomicRootValue]) hfactor
  simp only [one_pow, one_mul] at hcomp
  have hv := complementFactor_eval_eq_regularized (Icc 1 N) (rootSlots N w) hS i
  rw [hcomp] at hv
  exact hv.symm

noncomputable def vanishingPowerProduct (N : ℕ) (w : ℕ → ℕ) (t : ℕ) : ℝ :=
  ∏ i ∈ range N, if t ∣ i + 1 then ((i + 1 : ℕ) : ℝ) ^ w i else 1

theorem vanishingPowerProduct_nonneg (N : ℕ) (w : ℕ → ℕ) (t : ℕ) :
    0 ≤ vanishingPowerProduct N w t := by
  apply prod_nonneg
  intro i _
  split_ifs
  · exact pow_nonneg (Nat.cast_nonneg _) _
  · exact zero_le_one

theorem vanishingPowerProduct_le (N : ℕ) (w : ℕ → ℕ) (t : ℕ) :
    vanishingPowerProduct N w t ≤ (N : ℝ) ^ rootSlots N w t := by
  calc
    vanishingPowerProduct N w t ≤
        ∏ i ∈ range N, (N : ℝ) ^ (if t ∣ i + 1 then w i else 0) := by
      apply prod_le_prod₀
      · intro i _
        split_ifs
        · exact pow_nonneg (Nat.cast_nonneg _) _
        · exact zero_le_one
      · intro i hi
        by_cases hd : t ∣ i + 1
        · simp only [ite_eq_left hd]
          have hle : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle _
        · simp only [ite_eq_right hd, pow_zero, le_refl]
    _ = (N : ℝ) ^ rootSlots N w t := by rw [prod_pow_eq_pow_sum]; rfl

theorem flat_regularizedNorm_formula
    (N : ℕ) (w : ℕ → ℕ) (p k : ℕ) (hp : p.Prime)
    (ht : p ^ (k + 1) ∈ Icc 1 N) :
    regularizedCyclotomicNorm (Icc 1 N) (rootSlots N w) (p ^ (k + 1)) =
      vanishingPowerProduct N w (p ^ (k + 1)) ^ (p ^ (k + 1)).totient *
        (p : ℝ) ^ nonvanishingPrimeWeight N w p (k + 1) := by
  let t := p ^ (k + 1)
  have hstart : regularizedCyclotomicNorm (Icc 1 N) (rootSlots N w) t =
      ∏ i ∈ range N, (∏ z ∈ primitiveRoots t ℂ,
        ‖(regularizedPowerFactor t (i + 1) z).eval z‖) ^ w i := by
    unfold regularizedCyclotomicNorm
    trans ∏ z ∈ primitiveRoots t ℂ, ∏ i ∈ range N,
      ‖(regularizedPowerFactor t (i + 1) z).eval z‖ ^ w i
    · apply prod_congr rfl
      intro z hz
      rw [flat_regularizedValue_eq N w t ht z hz]
      simp only [regularizedPowerProduct, eval_prod, norm_prod, eval_pow, norm_pow]
    · rw [prod_comm]
      apply prod_congr rfl
      intro i _
      exact Finset.prod_pow _ _ _
  rw [hstart]
  trans ∏ i ∈ range N,
    (if t ∣ i + 1 then ((i + 1 : ℕ) : ℝ) ^ w i else 1) ^ t.totient *
      (p : ℝ) ^ (if t ∣ i + 1 then 0 else w i * p ^ (i + 1).factorization p)
  · apply prod_congr rfl
    intro i _
    rw [regularizedPowerFactor_primitive_norm_product p k (i + 1) hp (by omega)]
    by_cases hd : t ∣ i + 1
    · simp only [t] at hd ⊢
      simp only [ite_eq_left hd, pow_zero, mul_one, ← pow_mul, Nat.mul_comm]
    · simp only [t] at hd ⊢
      simp only [ite_eq_right hd, one_pow, one_mul, ← pow_mul, Nat.mul_comm]
  · simp only [prod_mul_distrib, Finset.prod_pow, prod_pow_eq_pow_sum,
      vanishingPowerProduct, nonvanishingPrimeWeight, t]

theorem flat_regularizedNorm_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    regularizedCyclotomicNorm (Icc 1 N) (rootSlots N w) (p ^ (k + 1)) ≤
      ((N : ℝ) ^ rootSlots N w (p ^ (k + 1))) ^ (p ^ (k + 1)).totient *
        (p : ℝ) ^ ((k + 1) * weightMass N w) := by
  rw [flat_regularizedNorm_formula N w p k hp ht]
  have hv := vanishingPowerProduct_le N w (p ^ (k + 1))
  have hn := vanishingPowerProduct_nonneg N w (p ^ (k + 1))
  have he := nonvanishingPrimeWeight_le_mass hw p (k + 1) hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  gcongr

end Erdos345
