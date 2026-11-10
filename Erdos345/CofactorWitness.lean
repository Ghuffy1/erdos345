import Erdos345.IntegralTopCoefficient

namespace Erdos345

open Finset Polynomial

/-- An integer polynomial whose value at z is the initial filtered value
obtained by dividing the recurrence polynomial by X-z. -/
noncomputable def cofactorWitness (P : ℤ[X]) (f : ℕ → ℤ) : ℤ[X] :=
  ∑ n ∈ range P.natDegree,
    C (f n) * ∑ h ∈ Icc (n + 1) P.natDegree, C (P.coeff h) * X ^ (h - (n + 1))

theorem cofactorWitness_eval (P : ℤ[X]) (f : ℕ → ℤ) (z : ℂ)
    (hD : 0 < P.natDegree) :
    (cofactorWitness P f).eval₂ (Int.castRingHom ℂ) z =
      shiftAction (P.map (Int.castRingHom ℂ) /ₘ (X - C z)) (fun n => (f n : ℂ)) 0 := by
  have hmap : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) (Int.cast_injective (α := ℂ)) P
  have hq : (P.map (Int.castRingHom ℂ) /ₘ (X - C z)).natDegree < P.natDegree := by
    rw [natDegree_divByMonic _ (monic_X_sub_C z), natDegree_X_sub_C, hmap]
    omega
  rw [shiftAction_sum_of_degree_lt _ _ hq]
  simp only [cofactorWitness, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    Nat.zero_add]
  apply sum_congr rfl
  intro n _
  rw [coeff_divByMonic_X_sub_C, hmap]
  simp only [coeff_map, sum_mul, mul_sum, Int.coe_castRingHom]
  apply sum_congr rfl
  intro h _
  ring

theorem componentFilter_mul_linear {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) (hmi : 0 < m i) :
    componentFilter z m i * (X - C (z i)) = linearFactorProduct z m := by
  classical
  have heq : linearFactorProduct z m = complementFactor z m i * (X - C (z i)) ^ m i :=
    (prod_erase_mul _ _ (mem_univ i)).symm
  rw [heq, componentFilter, mul_assoc, ← pow_succ, Nat.sub_add_cancel hmi]

theorem componentFilter_eq_div {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) (i : I) (hmi : 0 < m i) :
    componentFilter z m i = linearFactorProduct z m /ₘ (X - C (z i)) := by
  rw [← componentFilter_mul_linear z m i hmi, mul_comm (componentFilter z m i),
    mul_divByMonic_cancel_left _ (monic_X_sub_C (z i))]

/-- All conjugate top witnesses are values of the same integer polynomial. -/
theorem cofactorWitness_eq_top
    {I : Type*} [Fintype I] (z : I → ℂ) (m : I → ℕ)
    (P : ℤ[X]) (hD : 0 < P.natDegree)
    (hsplit : linearFactorProduct z m = P.map (Int.castRingHom ℂ))
    (f : ℕ → ℤ) (c : (Σ i, Fin (m i)) → ℂ)
    (hrep : (fun n => (f n : ℂ)) = ∑ ij, c ij • exponentialPower (z ij.1) ij.2)
    (i : I) (hmi : 0 < m i) :
    (cofactorWitness P f).eval₂ (Int.castRingHom ℂ) (z i) =
      c ⟨i, ⟨m i - 1, by omega⟩⟩ *
        ((z i ^ (m i - 1) * ((m i - 1).factorial : ℂ)) *
          (complementFactor z m i).eval (z i)) := by
  rw [cofactorWitness_eval P f (z i) hD, ← hsplit, ← componentFilter_eq_div z m i hmi]
  exact componentFilter_expansion_at_zero z m _ c hrep i hmi

end Erdos345
