import Erdos345.CyclotomicChebyshevEnergy

namespace Erdos345

open Finset

def padFin {R : Type*} [Zero R] {m D : ℕ} (a : Fin m → R) (j : Fin D) : R :=
  if h : j.val < m then a ⟨j.val, h⟩ else 0

theorem padFin_castLE {R : Type*} [Zero R] {m D : ℕ}
    (a : Fin m → R) (hm : m ≤ D) (i : Fin m) :
    padFin a (Fin.castLE hm i) = a i := by
  simp [padFin, i.isLt]

theorem padFin_eq_zero {R : Type*} [Zero R] {m D : ℕ}
    (a : Fin m → R) (j : Fin D) (hj : m ≤ j.val) : padFin a j = 0 := by
  simp only [padFin, dite_eq_right (by omega : ¬j.val < m)]

theorem sum_padFin_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {m D : ℕ} (a : Fin m → R) (hm : m ≤ D) (v : Fin D → M) :
    (∑ j : Fin D, padFin a j • v j) = ∑ i : Fin m, a i • v (Fin.castLE hm i) := by
  classical
  let S := (univ : Finset (Fin m)).image (Fin.castLE hm)
  calc
    _ = ∑ j ∈ S, padFin a j • v j := by
      symm
      apply sum_subset (subset_univ S)
      intro j _ hj
      have hlarge : m ≤ j.val := by
        by_contra h
        have hjm : j.val < m := by omega
        have heq : Fin.castLE hm (⟨j.val, hjm⟩ : Fin m) = j := by apply Fin.ext; rfl
        exact hj (mem_image.mpr ⟨⟨j.val, hjm⟩, mem_univ _, heq⟩)
      rw [padFin_eq_zero a j hlarge, zero_smul]
    _ = _ := by
      rw [show S = (univ : Finset (Fin m)).image (Fin.castLE hm) from rfl,
        sum_image (fun _ _ _ _ h => Fin.castLE_injective hm h)]
      apply sum_congr rfl
      intro i _
      rw [padFin_castLE]

end Erdos345
