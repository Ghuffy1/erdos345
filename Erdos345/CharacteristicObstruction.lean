import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.ZMod.Basic

/-!
The characteristic-polynomial obstruction in local scaling. A coordinate
equal to one suffices over every commutative ring, including a residue ring
with zero divisors. No field or prime-modulus hypothesis is used.
-/

namespace Erdos345

open Matrix Polynomial

theorem characteristic_eq_zero_of_unit_coordinate {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (v : ι → R) (t : R)
    (heigen : A *ᵥ v = t • v) {i : ι} (hi : v i = 1) :
    A.charpoly.eval t = 0 := by
  have hscalar : Matrix.scalar ι t = t • (1 : Matrix ι ι R) := by
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.scalar, hjk]
  have hker : (Matrix.scalar ι t - A) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hscalar, Matrix.smul_mulVec, Matrix.one_mulVec, heigen, sub_self]
  rw [Matrix.eval_charpoly]
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker (by
    rw [hi]
    exact one_mem _)

theorem characteristic_dvd_of_congruence {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (v : ι → ℤ) (t : ℤ) (q : ℕ)
    (heigen : ∀ i, (q : ℤ) ∣ (A *ᵥ v) i - t * v i)
    (hunit : ∃ i, v i = 1) :
    (q : ℤ) ∣ A.charpoly.eval t := by
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  have hmap : A.map φ *ᵥ (φ ∘ v) = φ t • (φ ∘ v) := by
    funext i
    have hzero : φ ((A *ᵥ v) i - t * v i) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (heigen i)
    simp only [map_sub, map_mul] at hzero
    change (A.map φ *ᵥ (φ ∘ v)) i = φ t * φ (v i)
    rw [← RingHom.map_mulVec]
    exact sub_eq_zero.mp hzero
  obtain ⟨i, hi⟩ := hunit
  have hchar := characteristic_eq_zero_of_unit_coordinate (A.map φ) (φ ∘ v) (φ t)
    hmap (i := i) (by simp [hi])
  rw [Matrix.charpoly_map, Polynomial.eval_map_apply] at hchar
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hchar

end Erdos345
