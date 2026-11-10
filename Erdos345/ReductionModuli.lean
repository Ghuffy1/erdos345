import Erdos345.NewtonCoefficients
import Mathlib.Algebra.GCDMonoid.Finset

namespace Erdos345

def reductionIndices (k d : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun j => d < j)

/-- The exact gcd of the higher integral Newton coefficients. -/
def reductionModulus (k d : ℕ) : ℕ :=
  (reductionIndices k d).gcd (powerCoefficient k)

theorem dvd_reductionModulus_iff (q k d : ℕ) :
    q ∣ reductionModulus k d ↔
      ∀ j : ℕ, d < j → q ∣ powerCoefficient k j := by
  rw [reductionModulus, Finset.dvd_gcd_iff]
  constructor
  · intro h j hj
    by_cases hjk : j ≤ k
    · exact h j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩)
    · rw [powerCoefficient_eq_zero (by omega)]
      exact dvd_zero q
  · intro h j hj
    exact h j (Finset.mem_filter.mp hj).2

theorem hasNewtonReduction_iff_dvd (q k d : ℕ) :
    hasNewtonReduction q k d ↔ q ∣ reductionModulus k d :=
  (hasNewtonReduction_iff q k d).trans (dvd_reductionModulus_iff q k d).symm

theorem factorial_dvd_reductionModulus (k d : ℕ) :
    d.factorial ∣ reductionModulus k d := by
  rw [dvd_reductionModulus_iff]
  intro j hj
  exact (Nat.factorial_dvd_factorial (Nat.le_of_lt hj)).trans
    (dvd_mul_right j.factorial (Nat.stirlingSecond k j))

theorem reductionModulus_mono_dvd (k : ℕ) {d e : ℕ} (hde : d ≤ e) :
    reductionModulus k d ∣ reductionModulus k e := by
  rw [dvd_reductionModulus_iff]
  intro j hj
  exact (dvd_reductionModulus_iff _ _ _).mp dvd_rfl j (hde.trans_lt hj)

theorem powerCoefficient_one {k : ℕ} (hk : 0 < k) : powerCoefficient k 1 = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp [powerCoefficient, Nat.stirlingSecond_one_right]

theorem reductionModulus_zero {k : ℕ} (hk : 0 < k) :
    reductionModulus k 0 = 1 := by
  apply Nat.dvd_one.mp
  have h : reductionModulus k 0 ∣ powerCoefficient k 1 :=
    (dvd_reductionModulus_iff _ _ _).mp dvd_rfl 1 (by omega)
  simpa [powerCoefficient_one hk] using h

theorem reductionModulus_step (k d : ℕ) :
    reductionModulus k d =
      Nat.gcd (powerCoefficient k (d + 1)) (reductionModulus k (d + 1)) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (dvd_reductionModulus_iff _ _ _).mp dvd_rfl (d + 1) (by omega)
    · exact reductionModulus_mono_dvd k (by omega)
  · rw [dvd_reductionModulus_iff]
    intro j hj
    by_cases he : j = d + 1
    · rw [he]
      exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans
        ((dvd_reductionModulus_iff _ _ _).mp dvd_rfl j (by omega))

end Erdos345
