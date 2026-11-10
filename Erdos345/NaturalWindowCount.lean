import Erdos345.GridArcCount

namespace Erdos345

noncomputable def naturalWindow (a b : ℝ) : Finset ℕ := Finset.Icc ⌈a⌉₊ ⌊b⌋₊

theorem mem_naturalWindow (a b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    n ∈ naturalWindow a b ↔ a ≤ n ∧ (n : ℝ) ≤ b := by
  simp only [naturalWindow, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb]

/-- A nonnegative real interval of length at least two contains at
least half its length in natural numbers. -/
theorem naturalWindow_card_half_length (a b : ℝ) (ha : 0 ≤ a) (hlen : 2 ≤ b - a) :
    (b - a) / 2 ≤ ((naturalWindow a b).card : ℝ) := by
  let m := ⌈a⌉₊
  let n := ⌊b⌋₊
  have hm : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have hn : b < (n : ℝ) + 1 := Nat.lt_floor_add_one b
  have hmnR : (m : ℝ) ≤ n := by linarith
  have hmn : m ≤ n := by exact_mod_cast hmnR
  have hcard : ((naturalWindow a b).card : ℝ) = (n : ℝ) + 1 - m := by
    change (((Finset.Icc m n).card : ℕ) : ℝ) = _
    rw [Nat.card_Icc, Nat.cast_sub (show m ≤ n + 1 by omega), Nat.cast_add, Nat.cast_one]
  rw [hcard]
  linarith

end Erdos345
