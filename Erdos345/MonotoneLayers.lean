import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega

namespace Erdos345

open Finset

def weightMass (N : ℕ) (a : ℕ → ℕ) : ℕ := ∑ i ∈ range N, a i

def weightLayer (N : ℕ) (a : ℕ → ℕ) (r : ℕ) : Finset ℕ :=
  (range N).filter fun i => r < a i

def layerHeight (N : ℕ) (a : ℕ → ℕ) (r : ℕ) : ℕ := (weightLayer N a r).card

theorem weight_le_mass {N : ℕ} (a : ℕ → ℕ) {i : ℕ} (hi : i < N) :
    a i ≤ weightMass N a :=
  single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)

theorem initial_finset_eq_range_card (S : Finset ℕ)
    (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S) : S = range S.card := by
  apply eq_of_subset_of_card_le
  · intro i hi
    apply mem_range.mpr
    have hsub : range (i + 1) ⊆ S := by
      intro j hj
      exact hS i hi j (by have := mem_range.mp hj; omega)
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    omega
  · simp

theorem weightLayer_eq_range {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) (r : ℕ) :
    weightLayer N a r = range (layerHeight N a r) := by
  apply initial_finset_eq_range_card
  intro i hi j hji
  obtain ⟨hiN, hra⟩ := mem_filter.mp hi
  have hiN' := mem_range.mp hiN
  have hjN : j < N := hji.trans_lt hiN'
  exact mem_filter.mpr ⟨mem_range.mpr hjN, hra.trans_le (ha hjN hiN' hji)⟩

theorem layerHeight_le {N : ℕ} {a : ℕ → ℕ} (r : ℕ) : layerHeight N a r ≤ N := by
  exact (card_filter_le _ _).trans (by simp)

theorem layer_index_count {N : ℕ} (a : ℕ → ℕ) {i : ℕ} (hi : i < N) :
    ((range (weightMass N a)).filter fun r => r < a i).card = a i := by
  have heq : (range (weightMass N a)).filter (fun r => r < a i) = range (a i) := by
    ext r
    simp only [mem_filter, mem_range]
    constructor
    · exact And.right
    · intro hr
      exact ⟨hr.trans_le (weight_le_mass a hi), hr⟩
  rw [heq, card_range]

theorem layer_weighted_sum (N : ℕ) (a f : ℕ → ℕ) :
    (∑ r ∈ range (weightMass N a), ∑ i ∈ weightLayer N a r, f i) =
      ∑ i ∈ range N, a i * f i := by
  simp only [weightLayer, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [← sum_filter, sum_const, layer_index_count a (mem_range.mp hi), nsmul_eq_mul]
  simp only [Nat.cast_id]

theorem sum_layerHeight (N : ℕ) (a : ℕ → ℕ) :
    (∑ r ∈ range (weightMass N a), layerHeight N a r) = weightMass N a := by
  have h := layer_weighted_sum N a (fun _ => 1)
  simpa only [sum_const, one_mul, mul_one, nsmul_eq_mul, Nat.cast_id,
    layerHeight, weightMass] using h

theorem layer_weighted_product {R : Type*} [CommMonoid R]
    (N : ℕ) (a : ℕ → ℕ) (f : ℕ → R) :
    (∏ r ∈ range (weightMass N a), ∏ i ∈ weightLayer N a r, f i) =
      ∏ i ∈ range N, f i ^ a i := by
  simp only [weightLayer, prod_filter]
  rw [prod_comm]
  apply prod_congr rfl
  intro i hi
  rw [← prod_filter, prod_const, layer_index_count a (mem_range.mp hi)]

def normalizedMoment (N : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range N, (i + 1) ^ a i

theorem normalizedMoment_eq_layer_factorials {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) :
    normalizedMoment N a = ∏ r ∈ range (weightMass N a), (layerHeight N a r).factorial := by
  rw [normalizedMoment, ← layer_weighted_product N a (fun i : ℕ => i + 1)]
  apply prod_congr rfl
  intro r _
  rw [weightLayer_eq_range ha, prod_range_add_one_eq_factorial]

/-- The nonincreasing multiplicities are essential to this factorial bound. -/
theorem normalizedMoment_dvd_factorial {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) :
    normalizedMoment N a ∣ (weightMass N a).factorial := by
  rw [normalizedMoment_eq_layer_factorials ha]
  have h := Nat.prod_factorial_dvd_factorial_sum (range (weightMass N a)) (layerHeight N a)
  simpa only [sum_layerHeight] using h

theorem normalizedMoment_pos (N : ℕ) (a : ℕ → ℕ) : 0 < normalizedMoment N a := by
  apply prod_pos
  intro i _
  exact pow_pos (Nat.succ_pos i) _

def rootSlots (N : ℕ) (a : ℕ → ℕ) (v : ℕ) : ℕ :=
  ∑ i ∈ range N, if v ∣ i + 1 then a i else 0

theorem rootSlots_eq_layer_quotients {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) (v : ℕ) :
    rootSlots N a v = ∑ r ∈ range (weightMass N a), layerHeight N a r / v := by
  have h := layer_weighted_sum N a (fun i => if v ∣ i + 1 then 1 else 0)
  have hright : (∑ i ∈ range N, a i * if v ∣ i + 1 then 1 else 0) = rootSlots N a v := by
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hright] at h
  rw [← h]
  apply sum_congr rfl
  intro r _
  rw [weightLayer_eq_range ha, ← card_filter, Nat.card_multiples]

/-- At most mass/v factors vanish at a root of exact order v. -/
theorem rootSlots_mul_le_mass {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) (v : ℕ) :
    v * rootSlots N a v ≤ weightMass N a := by
  calc
    v * rootSlots N a v =
        ∑ r ∈ range (weightMass N a), v * (layerHeight N a r / v) := by
      rw [rootSlots_eq_layer_quotients ha, mul_sum]
    _ ≤ ∑ r ∈ range (weightMass N a), layerHeight N a r := by
      apply sum_le_sum
      intro r _
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self (layerHeight N a r) v
    _ = weightMass N a := sum_layerHeight N a

end Erdos345
