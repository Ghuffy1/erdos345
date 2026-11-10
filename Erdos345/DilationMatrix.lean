import Erdos345.CharacteristicObstruction
import Erdos345.RecurrenceCongruence
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Erdos345

open Matrix Polynomial

noncomputable def recurrenceSolver (p : ℤ[X]) :
    (Fin p.natDegree → ℤ) →ₗ[ℤ] (ℕ → ℤ) :=
  (polynomialRecurrence p).solSpace.subtype.comp
    (polynomialRecurrence p).toInit.symm.toLinearMap

theorem recurrenceSolver_apply (p : ℤ[X]) (v : Fin p.natDegree → ℤ) (n : ℕ) :
    recurrenceSolver p v n = generatedRecurrence p v n := rfl

noncomputable def sampleDilated (D g : ℕ) : (ℕ → ℤ) →ₗ[ℤ] (Fin D → ℤ) where
  toFun f i := f (g * i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def dilationLinear (p : ℤ[X]) (g : ℕ) :
    (Fin p.natDegree → ℤ) →ₗ[ℤ] (Fin p.natDegree → ℤ) :=
  (sampleDilated p.natDegree g).comp (recurrenceSolver p)

noncomputable def dilationMatrix (p : ℤ[X]) (g : ℕ) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) ℤ :=
  LinearMap.toMatrix' (dilationLinear p g)

theorem dilationMatrix_mulVec (p : ℤ[X]) (g : ℕ) (v : Fin p.natDegree → ℤ)
    (i : Fin p.natDegree) :
    (dilationMatrix p g *ᵥ v) i = generatedRecurrence p v (g * i) := by
  rw [dilationMatrix, LinearMap.toMatrix'_mulVec]
  rfl

def powerInitial (p : ℤ[X]) (k : ℕ) : Fin p.natDegree → ℤ :=
  fun i => ((i : ℕ) : ℤ) ^ k

theorem dilation_power_congruence (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (q k g : ℕ)
    (hpower : ∀ n, (q : ℤ) ∣ shiftAction p (fun j : ℕ => (j : ℤ) ^ k) n)
    (i : Fin p.natDegree) :
    (q : ℤ) ∣ (dilationMatrix p g *ᵥ powerInitial p k) i - (g : ℤ) ^ k * powerInitial p k i := by
  rw [dilationMatrix_mulVec]
  change (q : ℤ) ∣ generatedRecurrence p (fun j : Fin p.natDegree => ((j : ℕ) : ℤ) ^ k)
    (g * i) - (g : ℤ) ^ k * ((i : ℕ) : ℤ) ^ k
  have h := generated_power_congruence p hunit q k hpower (g * i)
  simpa only [Nat.cast_mul, mul_pow] using h

/-- The initial power vector contains a literal one when the order is at least
two, giving a primitive eigenvector modulo every modulus. -/
theorem dilation_characteristic_dvd (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (hD : 2 ≤ p.natDegree) (q k g : ℕ)
    (hpower : ∀ n, (q : ℤ) ∣ shiftAction p (fun j : ℕ => (j : ℤ) ^ k) n) :
    (q : ℤ) ∣ (dilationMatrix p g).charpoly.eval ((g : ℤ) ^ k) := by
  apply characteristic_dvd_of_congruence (dilationMatrix p g) (powerInitial p k) ((g : ℤ) ^ k) q
  · exact dilation_power_congruence p hunit q k g hpower
  · refine ⟨⟨1, by omega⟩, ?_⟩
    simp [powerInitial]

theorem power_annihilator_degree_ge_two (p : ℤ[X])
    (hunit : p.leadingCoeff ^ 2 = 1) (q k : ℕ) (hq : 1 < q) (hk : 0 < k)
    (hpower : ∀ n, (q : ℤ) ∣ shiftAction p (fun j : ℕ => (j : ℤ) ^ k) n) :
    2 ≤ p.natDegree := by
  by_contra h
  have hcases : p.natDegree = 0 ∨ p.natDegree = 1 := by omega
  have hqone : ¬ (q : ℤ) ∣ 1 := by
    intro hd
    have hdNat : q ∣ 1 := by exact_mod_cast hd
    have := Nat.dvd_one.mp hdNat
    omega
  have hd : (q : ℤ) ∣ p.leadingCoeff := by
    rcases hcases with hD | hD
    · have hc : p.coeff 0 = p.leadingCoeff := by rw [← hD, coeff_natDegree]
      simpa [shiftAction_sum, hD, hc] using hpower 1
    · have hc : p.coeff 1 = p.leadingCoeff := by rw [← hD, coeff_natDegree]
      have hzero := hpower 0
      simpa [shiftAction_sum, hD, Finset.sum_range_succ, hk.ne', hc] using hzero
  apply hqone
  rw [← hunit, pow_two]
  exact dvd_mul_of_dvd_left hd _

/-- The full characteristic-polynomial divisibility conclusion, with its
recurrence and primitive-coordinate premises discharged for positive powers. -/
theorem power_annihilator_characteristic_dvd (p : ℤ[X])
    (hunit : p.leadingCoeff ^ 2 = 1) (q k g : ℕ) (hq : 1 < q) (hk : 0 < k)
    (hpower : ∀ n, (q : ℤ) ∣ shiftAction p (fun j : ℕ => (j : ℤ) ^ k) n) :
    (q : ℤ) ∣ (dilationMatrix p g).charpoly.eval ((g : ℤ) ^ k) :=
  dilation_characteristic_dvd p hunit
    (power_annihilator_degree_ge_two p hunit q k hq hk hpower) q k g hpower

end Erdos345
