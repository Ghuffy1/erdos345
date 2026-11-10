import Erdos345.PrimePowerGeneralNorm

namespace Erdos345

open Finset

theorem primePowerValuation_le_divisor_sum
    (p a n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (hnot : ¬p ^ a ∣ n) :
    p ^ n.factorization p ≤ ∑ b ∈ range a, if p ^ b ∣ n then p ^ b else 0 := by
  have hv : n.factorization p < a := by
    by_contra h
    exact hnot ((hp.pow_dvd_iff_le_factorization hn).mpr (by omega))
  have hd : p ^ n.factorization p ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hle := single_le_sum
    (f := fun b => if p ^ b ∣ n then p ^ b else 0)
    (fun b _ => Nat.zero_le _) (mem_range.mpr hv)
  simpa only [ite_eq_left hd] using hle

def nonvanishingPrimeWeight (N : ℕ) (w : ℕ → ℕ) (p a : ℕ) : ℕ :=
  ∑ i ∈ range N, if p ^ a ∣ i + 1 then 0 else w i * p ^ (i + 1).factorization p

theorem nonvanishingPrimeWeight_le_slot_sum
    (N : ℕ) (w : ℕ → ℕ) (p a : ℕ) (hp : p.Prime) :
    nonvanishingPrimeWeight N w p a ≤ ∑ b ∈ range a, p ^ b * rootSlots N w (p ^ b) := by
  calc
    nonvanishingPrimeWeight N w p a ≤
        ∑ i ∈ range N, w i * ∑ b ∈ range a, if p ^ b ∣ i + 1 then p ^ b else 0 := by
      apply sum_le_sum
      intro i _
      by_cases hd : p ^ a ∣ i + 1
      · simp only [ite_eq_left hd]
        exact Nat.zero_le _
      · simp only [ite_eq_right hd]
        exact Nat.mul_le_mul_left (w i)
          (primePowerValuation_le_divisor_sum p a (i + 1) hp (by omega) hd)
    _ = ∑ b ∈ range a, p ^ b * rootSlots N w (p ^ b) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [rootSlots, mul_sum]
      apply sum_congr rfl
      intro i _
      split_ifs <;> simp [Nat.mul_comm]

/-- Monotone flat-product weights bound the total prime-power norm exponent.
No factor is counted as nonvanishing when its full root order divides it. -/
theorem nonvanishingPrimeWeight_le_mass
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (p a : ℕ) (hp : p.Prime) :
    nonvanishingPrimeWeight N w p a ≤ a * weightMass N w := by
  calc
    nonvanishingPrimeWeight N w p a ≤ ∑ b ∈ range a, p ^ b * rootSlots N w (p ^ b) :=
      nonvanishingPrimeWeight_le_slot_sum N w p a hp
    _ ≤ ∑ _b ∈ range a, weightMass N w := by
      apply sum_le_sum
      intro b _
      exact rootSlots_mul_le_mass hw (p ^ b)
    _ = a * weightMass N w := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]

end Erdos345
