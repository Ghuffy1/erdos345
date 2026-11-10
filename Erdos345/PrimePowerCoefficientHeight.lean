import Erdos345.TopDenominatorBudget

namespace Erdos345

open Finset Polynomial

def primitiveTopCoefficient (S : Finset ℕ) (m : ℕ → ℕ)
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (t : ℕ) (ht : t ∈ S) (hmt : 0 < m t) (z : ↥(primitiveRoots t ℂ)) : ℂ :=
  c ⟨⟨⟨t, ht⟩, z⟩, ⟨m t - 1, by change m t - 1 < m t; omega⟩⟩

theorem primitiveTopCoefficient_norm_identity
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℤ)
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (t : ℕ) (ht : t ∈ S) (hmt : 0 < m t) (z : ↥(primitiveRoots t ℂ)) :
    ‖(cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) z‖ =
      ‖primitiveTopCoefficient S m c t ht hmt z‖ * ((m t - 1).factorial : ℝ) *
        ‖regularizedCyclotomicValue S m t z‖ := by
  let i : CyclotomicRootIndex S := ⟨⟨t, ht⟩, z⟩
  have hz : ‖(z : ℂ)‖ = 1 :=
    ((isPrimitiveRoot_of_mem_primitiveRoots z.property).isOfFinOrder (Nat.ne_of_gt (hS t ht))).norm_eq_one
  have heq := cofactorWitness_eq_top (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m)
    (cyclotomicProduct S m) (cyclotomicProduct_degree_pos S m ht (hS t ht) hmt)
    (cyclotomicProduct_split S m hS) f c hrep i hmt
  rw [complementFactor_eval_eq_regularized S m hS i] at heq
  have hn := congrArg norm heq
  simp only [norm_mul, norm_pow, Complex.norm_natCast] at hn
  change ‖(cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) z‖ =
    ‖primitiveTopCoefficient S m c t ht hmt z‖ *
      ((‖(z : ℂ)‖ ^ (m t - 1) * ((m t - 1).factorial : ℝ)) *
        ‖regularizedCyclotomicValue S m t z‖) at hn
  rw [hz, one_pow, one_mul] at hn
  nlinarith [hn]

theorem primitiveTopCoefficient_product_identity
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℤ)
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (t : ℕ) (ht : t ∈ S) (hmt : 0 < m t) :
    (∏ z ∈ primitiveRoots t ℂ,
      ‖(cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) z‖) =
      (∏ z : ↥(primitiveRoots t ℂ), ‖primitiveTopCoefficient S m c t ht hmt z‖) *
        topDenominator S m t := by
  have hcard : Fintype.card ↥(primitiveRoots t ℂ) = t.totient := by
    rw [Fintype.card_coe]
    exact (Complex.isPrimitiveRoot_exp t (Nat.ne_of_gt (hS t ht))).card_primitiveRoots
  rw [← prod_coe_sort (primitiveRoots t ℂ)
    (fun z : ℂ => ‖(cofactorWitness (cyclotomicProduct S m) f).eval₂ (Int.castRingHom ℂ) z‖)]
  simp_rw [primitiveTopCoefficient_norm_identity S m hS f c hrep t ht hmt]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, Finset.card_univ, hcard,
    prod_coe_sort (primitiveRoots t ℂ) (fun z : ℂ => ‖regularizedCyclotomicValue S m t z‖)]
  unfold topDenominator regularizedCyclotomicNorm
  ring

theorem primitiveTopCoefficient_ne_zero
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (t : ℕ) (ht : t ∈ S) (hmt : 0 < m t) (z : ↥(primitiveRoots t ℂ)) :
    primitiveTopCoefficient S m c t ht hmt z ≠ 0 := by
  have hm := (cyclotomicProduct_split S m hS).trans
    (integer_minimal_cyclotomic_complex S m f hminimal)
  exact minimal_split_expansion_top_ne_zero (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m)
    (fun n => (f n : ℂ)) hm c hrep ⟨⟨t, ht⟩, z⟩ hmt

/-- A fully proved prime-power coefficient-height estimate for an integer
flat-recurrence sequence. The later energy/Gram estimate is separate. -/
theorem exists_large_primePower_top_coefficient
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (c : (Σ i : CyclotomicRootIndex (Icc 1 N), Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) =
      ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1))) :
    ∃ z : ↥(primitiveRoots (p ^ (k + 1)) ℂ),
      Real.exp (-(4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)) ≤
        ‖primitiveTopCoefficient (Icc 1 N) m c (p ^ (k + 1)) ht hmt z‖ := by
  classical
  let t := p ^ (k + 1)
  let S := Icc 1 N
  have hS : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have ht0 : 0 < t := pow_pos hp.pos _
  have hcard : Fintype.card ↥(primitiveRoots t ℂ) = t.totient := by
    rw [Fintype.card_coe]
    exact (Complex.isPrimitiveRoot_exp t (Nat.ne_of_gt ht0)).card_primitiveRoots
  let : Nonempty ↥(primitiveRoots t ℂ) := Fintype.card_pos_iff.mp
    (by rw [hcard]; exact Nat.totient_pos.mpr ht0)
  let g : ↥(primitiveRoots t ℂ) → ℝ := fun z => ‖primitiveTopCoefficient S m c t ht hmt z‖
  have hg : ∀ z, 0 < g z := fun z => norm_pos_iff.mpr
    (primitiveTopCoefficient_ne_zero S m hS f hminimal c hrep t ht hmt z)
  have hprod := minimal_cyclotomic_witness_norm_lower S m hS f hminimal ht hmt
  rw [primitiveTopCoefficient_product_identity S m hS f c hrep t ht hmt] at hprod
  have hbudget := log_topDenominator_le hw hMass m hm p k hp ht
  rw [← hcard] at hbudget
  exact exists_factor_ge_exp_neg g hg (topDenominator S m t)
    (4 * ((weightMass N w : ℝ) / t) * Real.log N) (topDenominator_pos S m hS t ht0) hprod hbudget

end Erdos345
