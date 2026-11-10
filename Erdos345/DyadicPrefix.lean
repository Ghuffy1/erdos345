import Erdos345.SimultaneousBounds
import Mathlib.Data.Nat.Log

namespace Erdos345

theorem dyadic_cover_below {d L : ℕ} (hd : 0 < d) (hL : d < 2 ^ L) :
    ∃ i : ℕ, i ≤ L ∧ d ≤ 2 ^ i ∧ 2 ^ i ≤ 2 * d := by
  let i := Nat.log 2 d + 1
  have hlog : Nat.log 2 d < L :=
    (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hd)).mpr hL
  have hlo : d < 2 ^ i :=
    (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hd)).mp (Nat.lt_succ_self _)
  have hbase : 2 ^ Nat.log 2 d ≤ d :=
    Nat.pow_le_of_le_log (Nat.ne_of_gt hd) le_rfl
  refine ⟨i, ?_, hlo.le, ?_⟩
  · dsimp [i]
    omega
  · calc
      2 ^ i = 2 * 2 ^ Nat.log 2 d := by simp [i, pow_succ, mul_comm]
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hbase

def backwardPrefix (f : ℤ → ℚ) (k : ℤ) (d : ℕ) : ℚ :=
  ∑ t ∈ Finset.range d, f (k - (t : ℤ) - 1)

theorem backwardPrefix_mono (f : ℤ → ℚ) (hf : ∀ z, 0 ≤ f z)
    (k : ℤ) {d D : ℕ} (h : d ≤ D) :
    backwardPrefix f k d ≤ backwardPrefix f k D := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro t _ _
  exact hf _

/-- Bounds at logarithmically many dyadic lengths control every shorter prefix. -/
theorem backwardPrefix_bound_of_dyadic (f : ℤ → ℚ) (hf : ∀ z, 0 ≤ f z)
    (k : ℤ) (L : ℕ) (B : ℚ) (hB : 0 ≤ B)
    (hgood : ∀ i : ℕ, i ≤ L → backwardPrefix f k (2 ^ i) ≤ (2 ^ i : ℕ) * B)
    {d : ℕ} (hd : 0 < d) (hlen : d < 2 ^ L) :
    backwardPrefix f k d ≤ 2 * (d : ℚ) * B := by
  obtain ⟨i, hi, hlow, hhigh⟩ := dyadic_cover_below hd hlen
  have hc : ((2 ^ i : ℕ) : ℚ) ≤ 2 * (d : ℚ) := by exact_mod_cast hhigh
  calc
    backwardPrefix f k d ≤ backwardPrefix f k (2 ^ i) :=
      backwardPrefix_mono f hf k hlow
    _ ≤ ((2 ^ i : ℕ) : ℚ) * B := hgood i hi
    _ ≤ 2 * (d : ℚ) * B := mul_le_mul_of_nonneg_right hc hB

end Erdos345
