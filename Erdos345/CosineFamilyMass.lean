import Erdos345.CosineMassInterpolation

namespace Erdos345

theorem weightMass_extend_of_support (w : ℕ → ℕ) (m N : ℕ) (hmN : m ≤ N)
    (hsupport : ∀ i, m ≤ i → w i = 0) : weightMass N w = weightMass m w := by
  unfold weightMass
  apply Eq.symm
  apply Finset.sum_subset (Finset.range_mono hmN)
  intro i _hi hnot
  have him : m ≤ i := by
    have hh : ¬ i < m := by simpa using hnot
    omega
  exact hsupport i him

theorem weightedSum_extend_of_support (w : ℕ → ℕ) (m N : ℕ) (hmN : m ≤ N)
    (hsupport : ∀ i, m ≤ i → w i = 0) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (w i : ℝ) * g i) = ∑ i ∈ Finset.range m, (w i : ℝ) * g i := by
  apply Eq.symm
  apply Finset.sum_subset (Finset.range_mono hmN)
  intro i _hi hnot
  have him : m ≤ i := by
    have hh : ¬ i < m := by simpa using hnot
    omega
  have hz := hsupport i him
  simp only [hz, Nat.cast_zero, zero_mul]

theorem interlaced_weightMass_step (w : ℕ → ℕ → ℕ) (m : ℕ)
    (hinterlace : ∀ i < m, w (m + 1) (i + 1) ≤ w m i) :
    weightMass (m + 1) (w (m + 1)) ≤ w (m + 1) 0 + weightMass m (w m) := by
  unfold weightMass
  rw [Finset.sum_range_succ']
  have hs := Finset.sum_le_sum (fun i hi => hinterlace i (Finset.mem_range.mp hi))
  omega

theorem weightMass_ge_length (w : ℕ → ℕ) (m : ℕ) (hpos : ∀ i < m, 1 ≤ w i) :
    m ≤ weightMass m w := by
  calc
    m = ∑ _i ∈ Finset.range m, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i hi => hpos i (Finset.mem_range.mp hi))

/-- The finite interlacing criterion used to adjust the coefficient
mass in Belov--Konyagin's construction. -/
theorem exact_cosine_mass_of_interlacing (N : ℕ) (hN : 0 < N)
    (w : ℕ → ℕ → ℕ) (a : ℕ → ℝ) (C : ℕ) (A : ℝ)
    (hsupport : ∀ m ≤ N, ∀ i, m ≤ i → w m i = 0)
    (hpos : ∀ m ≤ N, ∀ i < m, 1 ≤ w m i)
    (hmono : ∀ m ≤ N, Antitone (w m))
    (hinterlace : ∀ m < N, ∀ i < m, w (m + 1) (i + 1) ≤ w m i)
    (hhead : ∀ m ≤ N, w m 0 ≤ C)
    (hpositive : ∀ m ≤ N, ∀ θ : ℝ, 0 ≤ a m + ∑ i ∈ Finset.range m,
      (w m i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ))
    (hcost : ∀ m ≤ N, a m ≤ A) :
    ∃ v : ℕ → ℕ, ∃ b : ℝ,
      AntitoneOn v (Set.Iio N) ∧ weightMass N v = N ∧
      (∀ θ : ℝ, 0 ≤ b + ∑ i ∈ Finset.range N,
        (v i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧ b ≤ A + C := by
  apply interpolate_cosine_mass N hN w a C A
  · rw [weightMass_extend_of_support (w 0) 0 N (by omega) (hsupport 0 (by omega))]
    simp [weightMass]
  · intro m hmN
    rw [weightMass_extend_of_support (w m) m N hmN (hsupport m hmN)]
    exact weightMass_ge_length (w m) m (hpos m hmN)
  · intro m hmN
    rw [weightMass_extend_of_support (w (m + 1)) (m + 1) N (by omega)
      (hsupport (m + 1) (by omega)),
      weightMass_extend_of_support (w m) m N (by omega) (hsupport m (by omega))]
    have hs := interlaced_weightMass_step w m (hinterlace m hmN)
    have hc := hhead (m + 1) (by omega)
    omega
  · intro m hmN
    exact (hmono m hmN).antitoneOn (Set.Iio N)
  · intro m hmN θ
    rw [weightedSum_extend_of_support (w m) m N hmN (hsupport m hmN)]
    exact hpositive m hmN θ
  · exact hcost

end Erdos345
