import Erdos345.CosineFamilyMass
import Mathlib.Tactic

namespace Erdos345

noncomputable def countingProfileWeight (φ : ℝ → ℕ) (m i : ℕ) : ℕ := φ ((m : ℝ) / (i + 1 : ℕ))

theorem countingProfileWeight_antitone (φ : ℝ → ℕ) (hφ : Monotone φ) (m : ℕ) :
    Antitone (countingProfileWeight φ m) := by
  intro i j hij
  apply hφ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  push_cast
  nlinarith

theorem countingProfileWeight_support (φ : ℝ → ℕ)
    (hzero : ∀ x : ℝ, x < 1 → φ x = 0) (m i : ℕ) (hmi : m ≤ i) :
    countingProfileWeight φ m i = 0 := by
  apply hzero
  apply (div_lt_one (by positivity : (0 : ℝ) < (i + 1 : ℕ))).mpr
  exact_mod_cast (show m < i + 1 by omega)

theorem countingProfileWeight_pos (φ : ℝ → ℕ) (hφ : Monotone φ)
    (hone : 1 ≤ φ 1) (m i : ℕ) (him : i < m) : 1 ≤ countingProfileWeight φ m i := by
  apply hone.trans
  apply hφ
  apply (one_le_div (by positivity : (0 : ℝ) < (i + 1 : ℕ))).mpr
  exact_mod_cast (show i + 1 ≤ m by omega)

theorem countingProfileWeight_interlace (φ : ℝ → ℕ) (hφ : Monotone φ)
    (m i : ℕ) (him : i < m) :
    countingProfileWeight φ (m + 1) (i + 1) ≤ countingProfileWeight φ m i := by
  apply hφ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have himR : (i : ℝ) + 1 ≤ m := by exact_mod_cast (show i + 1 ≤ m by omega)
  push_cast
  nlinarith

/-- Exact total mass follows from the counting-profile base polynomials;
their analytic nonnegativity is kept as a visible hypothesis. -/
theorem exact_mass_from_counting_profile (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℕ) (hφ : Monotone φ)
    (hzero : ∀ x : ℝ, x < 1 → φ x = 0) (hone : 1 ≤ φ 1)
    (a : ℕ → ℝ) (A : ℝ)
    (hpositive : ∀ m ≤ N, ∀ θ : ℝ, 0 ≤ a m + ∑ i ∈ Finset.range m,
      (countingProfileWeight φ m i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ))
    (hcost : ∀ m ≤ N, a m ≤ A) :
    ∃ v : ℕ → ℕ, ∃ b : ℝ,
      AntitoneOn v (Set.Iio N) ∧ weightMass N v = N ∧
      (∀ θ : ℝ, 0 ≤ b + ∑ i ∈ Finset.range N,
        (v i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧ b ≤ A + φ (N : ℝ) := by
  apply exact_cosine_mass_of_interlacing N hN (countingProfileWeight φ) a (φ (N : ℝ)) A
  · intro m _ i him
    exact countingProfileWeight_support φ hzero m i him
  · intro m _ i him
    exact countingProfileWeight_pos φ hφ hone m i him
  · intro m _
    exact countingProfileWeight_antitone φ hφ m
  · intro m _ i him
    exact countingProfileWeight_interlace φ hφ m i him
  · intro m hmN
    simp only [countingProfileWeight, Nat.zero_add, Nat.cast_one, div_one]
    exact hφ (by exact_mod_cast hmN)
  · exact hpositive
  · exact hcost

end Erdos345
