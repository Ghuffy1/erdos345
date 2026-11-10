import Erdos345.SineBlockAbsolute
import Erdos345.DyadicPolynomialSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace Erdos345

noncomputable def dyadicSineLevel (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ P j, scaledSineBlock p (v j) (x / 2 ^ j)

theorem sum_nat_le_square_of_interval (P : Finset ℕ) (X : ℕ)
    (hP : P ⊆ Finset.Icc 1 X) : (∑ p ∈ P, (p : ℝ)) ≤ (X : ℝ) ^ 2 := by
  have hc : P.card ≤ X := by simpa using Finset.card_le_card hP
  have hs : (∑ p ∈ P, (p : ℝ)) ≤ (P.card : ℝ) * X := by
    calc
      _ ≤ ∑ _p ∈ P, (X : ℝ) := Finset.sum_le_sum (fun p hp => by
        exact_mod_cast (Finset.mem_Icc.mp (hP hp)).2)
      _ = _ := by simp
  have hcR : (P.card : ℝ) ≤ X := by exact_mod_cast hc
  nlinarith [Nat.cast_nonneg (α := ℝ) X]

theorem dyadicSineLevel_abs_bound (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q j : ℕ) (x : ℝ)
    (hP : P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2)) (hv : v j ≤ j + 1) :
    |dyadicSineLevel P v j x| ≤
      (Real.pi / 2 * (q : ℝ) ^ 2 * |x|) * ((j + 1 : ℕ) : ℝ) ^ 6 / 2 ^ j := by
  let C := Real.pi / 2 * |x| / 2 ^ j
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have heach : ∀ p ∈ P j, |scaledSineBlock p (v j) (x / 2 ^ j)| ≤ C * (v j : ℝ) ^ 2 * p := by
    intro p hp
    have hp0 : 0 < p := by have hh := (Finset.mem_Icc.mp (hP hp)).1; omega
    have hb := scaledSineBlock_abs_linear p (v j) hp0 (x / 2 ^ j)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ j)] at hb
    calc
      _ ≤ Real.pi / 2 * (p : ℝ) * (v j : ℝ) ^ 2 * (|x| / 2 ^ j) := hb
      _ = _ := by dsimp only [C]; ring
  have hs := sum_nat_le_square_of_interval (P j) (q * (j + 1) ^ 2) hP
  have hvR : (v j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hv
  have hv2 := pow_le_pow_left₀ (Nat.cast_nonneg (v j)) hvR 2
  calc
    |dyadicSineLevel P v j x| ≤ ∑ p ∈ P j, |scaledSineBlock p (v j) (x / 2 ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P j, C * (v j : ℝ) ^ 2 * p := Finset.sum_le_sum heach
    _ = C * (v j : ℝ) ^ 2 * (∑ p ∈ P j, (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ C * (v j : ℝ) ^ 2 * ((q * (j + 1) ^ 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C * ((j + 1 : ℕ) : ℝ) ^ 2 * ((q * (j + 1) ^ 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 hC) (by positivity)
    _ = _ := by dsimp only [C]; push_cast; ring

theorem summable_dyadicSineLevels (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q : ℕ) (x : ℝ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) : Summable (fun j => dyadicSineLevel P v j x) := by
  have h := (summable_succ_pow_div_two 6).mul_left (Real.pi / 2 * (q : ℝ) ^ 2 * |x|)
  apply h.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (Real.pi / 2 * (q : ℝ) ^ 2 * |x|) * ((j + 1 : ℕ) : ℝ) ^ 6 / 2 ^ j :=
      dyadicSineLevel_abs_bound P v q j x (hP j) (hv j)
    _ = _ := by ring

theorem dyadicSineLevel_nonneg_tail (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (r j : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hrj : r ≤ j) (hxr : x ≤ 2 ^ (r + 1))
    (hP : ∀ p ∈ P j, 0 < p) : 0 ≤ dyadicSineLevel P v j x := by
  have hpowers : (2 : ℝ) ^ r ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hrj
  have ht : x / 2 ^ j ≤ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    rw [pow_succ] at hxr
    nlinarith
  apply Finset.sum_nonneg
  intro p hp
  apply scaledSineBlock_nonneg p (v j) (hP p hp) (by positivity)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hP p hp
  linarith

end Erdos345
