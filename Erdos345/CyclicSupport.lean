import Erdos345.FiniteResidueDistribution

namespace Erdos345

noncomputable def residueCollision {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) : ℝ :=
  ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
    ‖cyclicFourier (fun r => (residueMass X r : ℂ)) h‖ ^ 2

theorem residueCollision_nonneg {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) : 0 ≤ residueCollision X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem residueCollision_identity {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) :
    residueCollision X + 1 = (q : ℝ) * ∑ r : ZMod q, residueMass X r ^ 2 := by
  have hz : cyclicFourier (fun r => (residueMass X r : ℂ)) (0 : ZMod q) = 1 := by
    rw [cyclicFourier_zero]
    exact_mod_cast residueMass_sum X
  have hnorm : (∑ r : ZMod q, ‖(residueMass X r : ℂ)‖ ^ 2) =
      ∑ r : ZMod q, residueMass X r ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _
    simp
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
    (fun h => ‖cyclicFourier (fun r => (residueMass X r : ℂ)) h‖ ^ 2) (Finset.mem_univ 0)
  rw [hz, norm_one, one_pow, cyclic_parseval, hnorm] at hsum
  exact hsum

theorem residueSupport_collision_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) :
    (q : ℝ) ≤ (residueSupport X).card * (residueCollision X + 1) := by
  let S := residueSupport X
  have hsum : (∑ r ∈ S, residueMass X r) = 1 := residueMass_sum_support X
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun r => residueMass X r)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum] at hcs
  have hsub : (∑ r ∈ S, residueMass X r ^ 2) ≤ ∑ r : ZMod q, residueMass X r ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg (α := ℝ) S.card)
  have hbase : (1 : ℝ) ≤ S.card * ∑ r : ZMod q, residueMass X r ^ 2 := by nlinarith only [hcs, hmul]
  calc
    (q : ℝ) = (q : ℝ) * 1 := (mul_one _).symm
    _ ≤ (q : ℝ) * (S.card * ∑ r : ZMod q, residueMass X r ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)
    _ = S.card * ((q : ℝ) * ∑ r : ZMod q, residueMass X r ^ 2) := by ring
    _ = _ := by rw [← residueCollision_identity X]

theorem residueSupport_large_of_collision_le_three {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {q : ℕ} [NeZero q] (X : Ω → ZMod q) (hX : residueCollision X ≤ 3) :
    (q : ℝ) / 4 ≤ (residueSupport X).card := by
  have h := residueSupport_collision_bound X
  have hmul := mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg (α := ℝ) (residueSupport X).card)
  nlinarith

end Erdos345
