import Erdos345.RecurrenceSpan
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Erdos345

open Finset Polynomial

abbrev CyclotomicRootIndex (S : Finset ℕ) :=
  Σ n : S, ↥(primitiveRoots (n : ℕ) ℂ)

def cyclotomicRootValue {S : Finset ℕ} (i : CyclotomicRootIndex S) : ℂ := i.2

def cyclotomicRootMultiplicity {S : Finset ℕ} (m : ℕ → ℕ)
    (i : CyclotomicRootIndex S) : ℕ := m i.1

theorem cyclotomicRootValue_injective (S : Finset ℕ) :
    Function.Injective (@cyclotomicRootValue S) := by
  rintro ⟨⟨n, hn⟩, ⟨a, ha⟩⟩ ⟨⟨m, hm⟩, ⟨b, hb⟩⟩ hab
  change a = b at hab
  have hna := isPrimitiveRoot_of_mem_primitiveRoots ha
  have hmb := isPrimitiveRoot_of_mem_primitiveRoots hb
  have hnm : n = m := hna.unique (hab.symm ▸ hmb)
  subst m
  subst b
  rfl

theorem cyclotomicRootValue_ne_zero (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (i : CyclotomicRootIndex S) : cyclotomicRootValue i ≠ 0 := by
  have hroot := isPrimitiveRoot_of_mem_primitiveRoots i.2.property
  exact hroot.ne_zero (Nat.ne_of_gt (hS i.1 i.1.property))

theorem cyclotomicProduct_split (S : Finset ℕ) (m : ℕ → ℕ)
    (hS : ∀ n ∈ S, 0 < n) :
    linearFactorProduct (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m) =
      (cyclotomicProduct S m).map (Int.castRingHom ℂ) := by
  classical
  rw [linearFactorProduct, Fintype.prod_sigma]
  have hinner (n : S) :
      (∏ z : ↥(primitiveRoots (n : ℕ) ℂ), (X - C (z : ℂ)) ^ m n) =
        (cyclotomic (n : ℕ) ℂ) ^ m n := by
    rw [Finset.prod_coe_sort (primitiveRoots (n : ℕ) ℂ)
      (fun z : ℂ => (X - C z) ^ m n), Finset.prod_pow]
    congr 1
    exact (cyclotomic_eq_prod_X_sub_primitiveRoots
      (Complex.isPrimitiveRoot_exp (n : ℕ) (Nat.ne_of_gt (hS n n.property)))).symm
  calc
    _ = ∏ n : S, (cyclotomic (n : ℕ) ℂ) ^ m n := by
      apply prod_congr rfl
      intro n _
      exact hinner n
    _ = ∏ n ∈ S, (cyclotomic n ℂ) ^ m n :=
      Finset.prod_coe_sort S (fun n => (cyclotomic n ℂ) ^ m n)
    _ = (cyclotomicProduct S m).map (Int.castRingHom ℂ) := by
      simp only [cyclotomicProduct, Polynomial.map_prod, Polynomial.map_pow, map_cyclotomic]

/-- Full exponential-polynomial representation for every complex solution of
an integer cyclotomic-product recurrence. All multiplicities are retained. -/
theorem cyclotomic_recurrence_expansion (S : Finset ℕ) (m : ℕ → ℕ)
    (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℂ)
    (hf : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℂ)) f = 0) :
    ∃ c : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ,
      f = ∑ ij, c ij • exponentialPower (cyclotomicRootValue ij.1) ij.2 := by
  apply split_recurrence_expansion (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m)
    (cyclotomicRootValue_injective S) (cyclotomicRootValue_ne_zero S hS)
  rwa [cyclotomicProduct_split S m hS]

end Erdos345
