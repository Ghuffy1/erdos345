import Erdos345.DyadicSineSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Fintype.BigOperators

namespace Erdos345

abbrev DyadicLevelIndex (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (j : ℕ) :=
  Σ p : P j, Fin ((p : ℕ) * v j)

abbrev DyadicSineIndex (P : ℕ → Finset ℕ) (v : ℕ → ℕ) :=
  Σ j : ℕ, DyadicLevelIndex P v j

noncomputable def dyadicAtomFrequency (j p i : ℕ) : ℝ :=
  (2 * (i : ℝ) + 1) / (2 ^ (j + 1) * (p : ℝ))

noncomputable def dyadicFrequency (P : ℕ → Finset ℕ) (v : ℕ → ℕ)
    (a : DyadicSineIndex P v) : ℝ :=
  dyadicAtomFrequency a.1 a.2.1 a.2.2

theorem dyadicAtomFrequency_nonneg (j p i : ℕ) : 0 ≤ dyadicAtomFrequency j p i := by
  unfold dyadicAtomFrequency
  positivity

theorem dyadicAtomFrequency_pos (j p i : ℕ) (hp : 0 < p) :
    0 < dyadicAtomFrequency j p i := by
  unfold dyadicAtomFrequency
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  positivity

theorem sum_dyadicAtomFrequency (j p v : ℕ) (hp : 0 < p) :
    (∑ i : Fin (p * v), dyadicAtomFrequency j p i) =
      (p : ℝ) * (v : ℝ) ^ 2 / 2 ^ (j + 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  unfold dyadicAtomFrequency
  rw [← Finset.sum_div, sum_odd_reals]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

theorem sum_dyadicFrequency_level (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (j : ℕ)
    (hP : ∀ p ∈ P j, 0 < p) :
    (∑ a : DyadicLevelIndex P v j, dyadicFrequency P v ⟨j, a⟩) =
      ∑ p ∈ P j, (p : ℝ) * (v j : ℝ) ^ 2 / 2 ^ (j + 1) := by
  rw [Fintype.sum_sigma]
  have heach : ∀ p : P j,
      (∑ i : Fin ((p : ℕ) * v j), dyadicFrequency P v ⟨j, ⟨p, i⟩⟩) =
        (p : ℝ) * (v j : ℝ) ^ 2 / 2 ^ (j + 1) := by
    intro p
    exact sum_dyadicAtomFrequency j p (v j) (hP p p.property)
  simp_rw [heach]
  exact Finset.sum_finset_coe (fun p : ℕ => (p : ℝ) * (v j : ℝ) ^ 2 / 2 ^ (j + 1)) (P j)

theorem dyadicFrequency_level_bound (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q j : ℕ)
    (hP : P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2)) (hv : v j ≤ j + 1) :
    (∑ a : DyadicLevelIndex P v j, dyadicFrequency P v ⟨j, a⟩) ≤
      ((q : ℝ) ^ 2 / 2) * ((j + 1 : ℕ) : ℝ) ^ 6 / 2 ^ j := by
  rw [sum_dyadicFrequency_level P v j (fun p hp => (Finset.mem_Icc.mp (hP hp)).1)]
  have hs := sum_nat_le_square_of_interval (P j) (q * (j + 1) ^ 2) hP
  have hvR : (v j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hv
  have hv2 := pow_le_pow_left₀ (Nat.cast_nonneg (v j)) hvR 2
  calc
    _ = (∑ p ∈ P j, (p : ℝ)) * (v j : ℝ) ^ 2 / 2 ^ (j + 1) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    _ ≤ ((q * (j + 1) ^ 2 : ℕ) : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (j + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hs hv2 (by positivity) (by positivity)
    _ = _ := by rw [pow_succ]; push_cast; ring

theorem summable_dyadicFrequency (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q : ℕ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) : Summable (dyadicFrequency P v) := by
  apply (summable_sigma_of_nonneg (f := dyadicFrequency P v)
    (fun a => dyadicAtomFrequency_nonneg a.1 a.2.1 a.2.2)).2
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  have hb := (summable_succ_pow_div_two 6).mul_left ((q : ℝ) ^ 2 / 2)
  apply hb.of_norm_bounded
  intro j
  have hnon : 0 ≤ ∑ a : DyadicLevelIndex P v j, dyadicFrequency P v ⟨j, a⟩ :=
    Finset.sum_nonneg (fun a _ => dyadicAtomFrequency_nonneg j a.1 a.2)
  rw [tsum_fintype, Real.norm_eq_abs, abs_of_nonneg hnon]
  calc
    _ ≤ ((q : ℝ) ^ 2 / 2) * ((j + 1 : ℕ) : ℝ) ^ 6 / 2 ^ j :=
      dyadicFrequency_level_bound P v q j (hP j) (hv j)
    _ = _ := by ring

end Erdos345
