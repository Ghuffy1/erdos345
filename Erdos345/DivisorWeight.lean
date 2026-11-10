import Erdos345.DivisorMean
import Erdos345.ShiftedAverages

namespace Erdos345

def divisorSupport (N : ℕ) : Finset ℤ :=
  (Finset.Ioc 0 N).image (fun n : ℕ => (n : ℤ))

def divisorWeight (N : ℕ) (z : ℤ) : ℚ :=
  if z ∈ divisorSupport N then (divisorCount z.toNat : ℚ) else 0

theorem divisorWeight_nonneg (N : ℕ) (z : ℤ) : 0 ≤ divisorWeight N z := by
  unfold divisorWeight
  split
  · exact Nat.cast_nonneg _
  · exact le_refl 0

theorem divisorWeight_zero (N : ℕ) (z : ℤ) (hz : z ∉ divisorSupport N) :
    divisorWeight N z = 0 := by
  simp [divisorWeight, hz]

theorem divisorWeight_nat {N n : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    divisorWeight N (n : ℤ) = (divisorCount n : ℚ) := by
  have hm : (n : ℤ) ∈ divisorSupport N :=
    Finset.mem_image.mpr ⟨n, Finset.mem_Ioc.mpr ⟨hn, hN⟩, rfl⟩
  simp [divisorWeight, hm]

theorem sum_divisorWeight (N : ℕ) :
    (∑ z ∈ divisorSupport N, divisorWeight N z) =
      ∑ n ∈ Finset.Ioc 0 N, (divisorCount n : ℚ) := by
  rw [divisorSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    exact divisorWeight_nat (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
  · intro a _ b _ hab
    exact Int.ofNat_injective hab

theorem sum_divisorWeight_le (N : ℕ) :
    (∑ z ∈ divisorSupport N, divisorWeight N z) ≤ (N : ℚ) * harmonic N := by
  rw [sum_divisorWeight]
  exact sum_divisorCount_le_harmonic N

end Erdos345
