import Erdos345.DyadicFrequency

namespace Erdos345

theorem sum_sine_dyadicFrequency_level (P : ℕ → Finset ℕ) (v : ℕ → ℕ)
    (j : ℕ) (x : ℝ) :
    (∑ a : DyadicLevelIndex P v j,
      Real.sin (Real.pi * x * dyadicFrequency P v ⟨j, a⟩)) =
      dyadicSineLevel P v j x := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ p : P j, scaledSineBlock p (v j) (x / 2 ^ j) := by
      apply Finset.sum_congr rfl
      intro p _
      change (∑ i : Fin ((p : ℕ) * v j),
        Real.sin (Real.pi * x * dyadicAtomFrequency j p i)) = _
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        Real.sin (Real.pi * x * dyadicAtomFrequency j p i))]
      unfold scaledSineBlock oddSineSum
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      unfold dyadicAtomFrequency
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = dyadicSineLevel P v j x := by
      unfold dyadicSineLevel
      exact Finset.sum_finset_coe (fun p : ℕ => scaledSineBlock p (v j) (x / 2 ^ j)) (P j)

theorem summable_sine_dyadicFrequency (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q : ℕ) (x : ℝ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) :
    Summable (fun a => Real.sin (Real.pi * x * dyadicFrequency P v a)) := by
  have hs := (summable_dyadicFrequency P v q hP hv).mul_left (Real.pi * |x|)
  apply hs.of_norm_bounded
  intro a
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |Real.pi * x * dyadicFrequency P v a| := Real.abs_sin_le_abs
    _ = Real.pi * |x| * dyadicFrequency P v a := by
      have hn : 0 ≤ dyadicFrequency P v a :=
        dyadicAtomFrequency_nonneg a.1 a.2.1 a.2.2
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_nonneg hn]

theorem summable_abs_sine_dyadicFrequency (P : ℕ → Finset ℕ) (v : ℕ → ℕ)
    (q : ℕ) (x : ℝ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) :
    Summable (fun a => |Real.sin (Real.pi * x * dyadicFrequency P v a)|) :=
  (summable_sine_dyadicFrequency P v q x hP hv).abs

theorem tsum_sine_dyadicFrequency (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q : ℕ) (x : ℝ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) :
    (∑' a, Real.sin (Real.pi * x * dyadicFrequency P v a)) =
      ∑' j, dyadicSineLevel P v j x := by
  rw [(summable_sine_dyadicFrequency P v q x hP hv).tsum_sigma]
  apply tsum_congr
  intro j
  rw [tsum_fintype]
  exact sum_sine_dyadicFrequency_level P v j x

end Erdos345
