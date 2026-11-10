import Erdos345.MinimalWitnessNorm
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

namespace Erdos345

open Finset Polynomial

theorem primitive_power_difference_product_eq_norm
    {n : ℕ} (hn : 0 < n) {L : Type*} [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {n} ℚ L] {z : L} (hz : IsPrimitiveRoot z n) (h : ℕ) :
    (∏ w ∈ primitiveRoots n ℂ, (w ^ h - 1)) =
      algebraMap ℚ ℂ (Algebra.norm ℚ (z ^ h - 1)) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  let : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ, ← Finset.prod_coe_sort (primitiveRoots n ℂ)
    (fun w : ℂ => w ^ h - 1)]
  symm
  apply Fintype.prod_equiv (hz.embeddingsEquivPrimitiveRoots ℂ (cyclotomic.irreducible_rat hn))
  intro σ
  simp only [map_sub, map_pow, map_one, IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe]

theorem prime_primitive_sub_one_norm_product (p : ℕ) (hp : p.Prime) :
    (∏ w ∈ primitiveRoots p ℂ, ‖w - 1‖) = (p : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpoly := cyclotomic_eq_prod_X_sub_primitiveRoots
    (Complex.isPrimitiveRoot_exp p hp.ne_zero)
  have hvalue := congrArg (Polynomial.eval (1 : ℂ)) hpoly
  simp only [eval_prod, eval_sub, eval_X, eval_C] at hvalue
  have hone : (cyclotomic p ℂ).eval 1 = (p : ℂ) := by
    simpa only [Nat.zero_add, pow_one] using (eval_one_cyclotomic_prime_pow (R := ℂ) (p := p) 0)
  calc
    (∏ w ∈ primitiveRoots p ℂ, ‖w - 1‖) = ∏ w ∈ primitiveRoots p ℂ, ‖1 - w‖ := by
      apply prod_congr rfl
      intro w _
      exact norm_sub_rev w 1
    _ = ‖∏ w ∈ primitiveRoots p ℂ, (1 - w)‖ := (norm_prod _ _).symm
    _ = (p : ℝ) := by rw [← hvalue, hone, Complex.norm_natCast]

/-- Exact product norm for nonvanishing prime-power exponents at primitive
p^(k+1)-th roots, including the prime-order and two-adic boundary cases. -/
theorem primePower_pure_power_norm_product
    (p k s : ℕ) (hp : p.Prime) (hs : s ≤ k) :
    (∏ w ∈ primitiveRoots (p ^ (k + 1)) ℂ, ‖w ^ (p ^ s) - 1‖) =
      (p : ℝ) ^ (p ^ s) := by
  classical
  by_cases hk : k = 0
  · have hs0 : s = 0 := by omega
    subst k
    subst s
    simpa only [Nat.zero_add, pow_zero, pow_one] using prime_primitive_sub_one_norm_product p hp
  · let L := CyclotomicField (p ^ (k + 1)) ℚ
    let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    let : NeZero ((p ^ (k + 1) : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)⟩
    let : IsCyclotomicExtension {p ^ (k + 1)} ℚ L :=
      CyclotomicField.isCyclotomicExtension (p ^ (k + 1)) ℚ
    let : Fact p.Prime := ⟨hp⟩
    let z : L := IsCyclotomicExtension.zeta (p ^ (k + 1)) ℚ L
    have hz : IsPrimitiveRoot z (p ^ (k + 1)) := IsCyclotomicExtension.zeta_spec _ _ _
    have hnorm := hz.norm_pow_sub_one_eq_prime_pow_of_ne_zero
      (cyclotomic.irreducible_rat (pow_pos hp.pos _)) hs hk
    have hprod := primitive_power_difference_product_eq_norm (pow_pos hp.pos _) hz (p ^ s)
    rw [hnorm] at hprod
    rw [← norm_prod, hprod]
    simp only [map_pow, map_natCast, norm_pow, Complex.norm_natCast]

end Erdos345
