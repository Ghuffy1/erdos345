import Erdos345.DivisorWeight
import Erdos345.DyadicPrefix
import Mathlib.Tactic.Ring

namespace Erdos345

def degreeInterval (Y : ℕ) : Finset ℤ :=
  (Finset.range (Y + 1)).image (fun n => ((Y + n : ℕ) : ℤ))

def dyadicShifts (i : ℕ) : Finset ℤ :=
  (Finset.range (2 ^ i)).image (fun n : ℕ => (n : ℤ) + 1)

theorem degreeInterval_card (Y : ℕ) : (degreeInterval Y).card = Y + 1 := by
  rw [degreeInterval, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  exact Nat.add_left_cancel (Int.ofNat_injective hab)

theorem degreeInterval_nonempty (Y : ℕ) : (degreeInterval Y).Nonempty := by
  refine ⟨(Y : ℤ), Finset.mem_image.mpr ⟨0, ?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (Nat.succ_pos Y)
  · simp

theorem dyadicShifts_card (i : ℕ) : (dyadicShifts i).card = 2 ^ i := by
  rw [dyadicShifts, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  exact Int.ofNat_injective (add_right_cancel hab)

theorem dyadicShifts_nonempty (i : ℕ) : (dyadicShifts i).Nonempty := by
  apply Finset.card_pos.mp
  rw [dyadicShifts_card]
  exact pow_pos (by decide) i

theorem sum_dyadicShifts (f : ℤ → ℚ) (k : ℤ) (i : ℕ) :
    (∑ t ∈ dyadicShifts i, f (k - t)) = backwardPrefix f k (2 ^ i) := by
  rw [dyadicShifts, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t _
    congr 1
    omega
  · intro a _ b _ hab
    exact Int.ofNat_injective (add_right_cancel hab)

theorem harmonic_nonneg (N : ℕ) : 0 ≤ harmonic N :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Every dyadic interval has a degree with all the selected dyadic prefix bounds.
Only the elementary global divisor mean is used. -/
theorem exists_good_dyadic_degree (Y L : ℕ) :
    ∃ k ∈ degreeInterval Y, ∀ i : ℕ, i ≤ L →
      backwardPrefix (divisorWeight (2 * Y)) k (2 ^ i) ≤
        (2 * ((L + 1 : ℕ) : ℚ) * harmonic (2 * Y)) * ((2 ^ i : ℕ) : ℚ) := by
  let B : ℚ := 2 * ((L + 1 : ℕ) : ℚ) * harmonic (2 * Y)
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (by decide) (Nat.cast_nonneg _)) (harmonic_nonneg _)
  have hbudget :
      ((Finset.range (L + 1)).card : ℚ) *
        (∑ u ∈ divisorSupport (2 * Y), divisorWeight (2 * Y) u) ≤
        ((degreeInterval Y).card : ℚ) * B := by
    rw [Finset.card_range, degreeInterval_card]
    calc
      ((L + 1 : ℕ) : ℚ) *
          (∑ u ∈ divisorSupport (2 * Y), divisorWeight (2 * Y) u) ≤
          ((L + 1 : ℕ) : ℚ) * ((2 * Y : ℕ) : ℚ) * harmonic (2 * Y) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (sum_divisorWeight_le (2 * Y)) (Nat.cast_nonneg (L + 1))
      _ = (Y : ℚ) * B := by dsimp [B]; push_cast; ring
      _ ≤ ((Y + 1 : ℕ) : ℚ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ Y) hB
  obtain ⟨k, hk, hgood⟩ := exists_simultaneous_backward_averages_support
    (Finset.range (L + 1)) (degreeInterval Y) (divisorSupport (2 * Y))
    dyadicShifts (divisorWeight (2 * Y)) (degreeInterval_nonempty Y)
    (fun i _ => dyadicShifts_nonempty i) (divisorWeight_zero (2 * Y))
    (divisorWeight_nonneg (2 * Y)) B hbudget
  refine ⟨k, hk, ?_⟩
  intro i hi
  have h := hgood i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  simpa only [sum_dyadicShifts, dyadicShifts_card] using h

theorem exists_good_prefix_degree (Y L : ℕ) :
    ∃ k ∈ degreeInterval Y, ∀ d : ℕ, 0 < d → d < 2 ^ L →
      backwardPrefix (divisorWeight (2 * Y)) k d ≤
        4 * (d : ℚ) * ((L + 1 : ℕ) : ℚ) * harmonic (2 * Y) := by
  obtain ⟨k, hk, hgood⟩ := exists_good_dyadic_degree Y L
  refine ⟨k, hk, ?_⟩
  intro d hd hlen
  have hB : 0 ≤ (2 * ((L + 1 : ℕ) : ℚ) * harmonic (2 * Y)) :=
    mul_nonneg (mul_nonneg (by decide) (Nat.cast_nonneg _)) (harmonic_nonneg _)
  have h := backwardPrefix_bound_of_dyadic (divisorWeight (2 * Y))
    (divisorWeight_nonneg (2 * Y)) k L
    (2 * ((L + 1 : ℕ) : ℚ) * harmonic (2 * Y)) hB
    (fun i hi => by simpa only [mul_comm] using hgood i hi) hd hlen
  convert h using 1; ring

/-- A fully finite, unconditional good-degree selection theorem.

The prefix on the left is the sum of tau(k-j) for 1 ≤ j ≤ d. The bound is
uniform over every d<k, rather than being selected afresh for each d.
-/
theorem exists_good_degree (Y : ℕ) (hY : 0 < Y) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ d : ℕ, 0 < d → d < k →
        (∑ t ∈ Finset.range d, (divisorCount (k - t - 1) : ℚ)) ≤
          4 * (d : ℚ) * ((Nat.log 2 (2 * Y) + 2 : ℕ) : ℚ) * harmonic (2 * Y) := by
  let L := Nat.log 2 (2 * Y) + 1
  have hlen : 2 * Y < 2 ^ L :=
    (Nat.log_lt_iff_lt_pow (by decide) (by omega : 2 * Y ≠ 0)).mp
      (Nat.lt_succ_self _)
  obtain ⟨k, hk, hgood⟩ := exists_good_prefix_degree Y L
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
  have hnY : n ≤ Y := by
    have := Finset.mem_range.mp hn
    omega
  refine ⟨Y + n, by omega, by omega, ?_⟩
  intro d hd hdk
  have hdlen : d < 2 ^ L := by omega
  have hraw := hgood d hd hdlen
  have heq :
      backwardPrefix (divisorWeight (2 * Y)) ((Y + n : ℕ) : ℤ) d =
        ∑ t ∈ Finset.range d, (divisorCount (Y + n - t - 1) : ℚ) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htd : t < d := Finset.mem_range.mp ht
    have hpos : 0 < Y + n - t - 1 := by omega
    have hle : Y + n - t - 1 ≤ 2 * Y := by omega
    have hz :
        ((Y + n : ℕ) : ℤ) - (t : ℤ) - 1 =
          ((Y + n - t - 1 : ℕ) : ℤ) := by omega
    rw [hz]
    exact divisorWeight_nat hpos hle
  rw [heq] at hraw
  simpa [L, Nat.add_assoc] using hraw

end Erdos345
