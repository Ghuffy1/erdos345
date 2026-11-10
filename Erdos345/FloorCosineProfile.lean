import Erdos345.TruncatedCosineBound

namespace Erdos345

theorem initialCosineSum_floor_eq (m : ℕ) (t θ : ℝ) (ht : 0 ≤ t) (htm : t ≤ m) :
    initialCosineSum ⌊t⌋₊ θ = ∑ i ∈ Finset.range m,
      if ((i + 1 : ℕ) : ℝ) ≤ t then Real.cos (θ * (i : ℝ) + θ) else 0 := by
  classical
  have hm := Nat.floor_le_of_le htm
  have heq : (Finset.range m).filter (fun i => ((i + 1 : ℕ) : ℝ) ≤ t) =
      Finset.range ⌊t⌋₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hi
      have h := (Nat.le_floor_iff ht).mpr hi.2
      omega
    · intro hi
      exact ⟨lt_of_lt_of_le hi hm, (Nat.le_floor_iff ht).mp (by omega)⟩
  rw [initialCosineSum, ← heq, Finset.sum_filter]

noncomputable def belovFloorCosine (q m : ℕ) (θ : ℝ) (a : BelovFamilyIndex q) : ℝ :=
  initialCosineSum ⌊(m : ℝ) / belovDenominator q a⌋₊ θ

theorem belovFloorCosine_zero_outside (q m : ℕ) (θ : ℝ) (a : BelovFamilyIndex q)
    (ha : a ∉ belovCutoff q m) : belovFloorCosine q m θ a = 0 := by
  have hlt : (m : ℝ) < belovDenominator q a := by
    exact lt_of_not_ge (fun h => ha ((mem_belovCutoff q m a).mpr h))
  have ht : (m : ℝ) / belovDenominator q a < 1 :=
    (div_lt_one (belovDenominator_pos q a)).mpr hlt
  simp [belovFloorCosine, Nat.floor_eq_zero.mpr ht, initialCosineSum]

theorem summable_belovFloorCosine (q m : ℕ) (θ : ℝ) : Summable (belovFloorCosine q m θ) := by
  apply summable_of_ne_finset_zero (s := belovCutoff q m)
  exact belovFloorCosine_zero_outside q m θ

theorem belovFloorCosine_eq_sum (q m : ℕ) (θ : ℝ) (a : BelovFamilyIndex q) :
    belovFloorCosine q m θ a = ∑ i ∈ Finset.range m,
      if a ∈ belovCutoff q ((m : ℝ) / ((i + 1 : ℕ) : ℝ))
        then Real.cos (θ * (i : ℝ) + θ) else 0 := by
  classical
  unfold belovFloorCosine
  rw [initialCosineSum_floor_eq m _ θ
    (div_nonneg (Nat.cast_nonneg m) (belovDenominator_pos q a).le)
    (div_le_self (Nat.cast_nonneg m) (one_le_belovDenominator q a))]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hcond : ((i + 1 : ℕ) : ℝ) ≤ (m : ℝ) / belovDenominator q a ↔
      a ∈ belovCutoff q ((m : ℝ) / ((i + 1 : ℕ) : ℝ)) := by
    rw [mem_belovCutoff, le_div_iff₀ (belovDenominator_pos q a), le_div_iff₀ hi]
    rw [mul_comm]
  simp only [hcond]

theorem tsum_belovFloorCosine (q m : ℕ) (θ : ℝ) :
    (∑' a, belovFloorCosine q m θ a) = ∑ i ∈ Finset.range m,
      (belovCountingProfile q ((m : ℝ) / ((i + 1 : ℕ) : ℝ)) : ℝ) *
        Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
  classical
  rw [tsum_eq_sum (s := belovCutoff q m) (belovFloorCosine_zero_outside q m θ)]
  simp_rw [belovFloorCosine_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let s := belovCutoff q ((m : ℝ) / ((i + 1 : ℕ) : ℝ))
  have hsub : s ⊆ belovCutoff q m := by
    intro a ha
    apply (mem_belovCutoff q m a).mpr
    have hm : (m : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ m :=
      div_le_self (Nat.cast_nonneg m) (by exact_mod_cast (show 1 ≤ i + 1 by omega))
    exact ((mem_belovCutoff q _ a).mp ha).trans hm
  calc
    _ = ∑ a ∈ s, if a ∈ s then Real.cos (θ * (i : ℝ) + θ) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro a _ ha
      exact ite_eq_right ha
    _ = (s.card : ℝ) * Real.cos (θ * (i : ℝ) + θ) := by simp
    _ = _ := by
      change _ = (s.card : ℝ) * _
      congr 2
      push_cast
      ring

end Erdos345
