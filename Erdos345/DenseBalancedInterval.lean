import Erdos345.DenseIntervalAddition
import Erdos345.FiniteSumsetSpan

namespace Erdos345

open scoped Classical Pointwise

/-- Two dense sumsets with balanced spans contain an interval whose
length is the sum of their density margins. -/
theorem interval_of_dense_balanced_sumsets (A B : Finset ℕ) (l m : ℕ)
    (hdA : natSetSpan A + m + 2 ≤ 2 * A.card)
    (hdB : natSetSpan B + m + 2 ≤ 2 * B.card)
    (hbalance : natSetSpan A ≤ natSetSpan B ∧ natSetSpan B ≤ natSetSpan A + l)
    (hl : l ≤ 2 * m) :
    ∃ a L : ℕ, 2 * m ≤ L ∧ ∀ g ∈ Finset.Icc a (a + L), g ∈ A + B := by
  let s := natSetSpan A + natSetSpan B
  let c := A.card + B.card - 2
  have hcardA := card_le_natSetSpan_add_one A
  have hcardB := card_le_natSetSpan_add_one B
  have hc : c ≤ s := by dsimp only [c, s]; omega
  have hd : s + 2 * m ≤ 2 * c := by dsimp only [c, s]; omega
  have hA : natSetSpan A + 2 ≤ A.card + B.card := by dsimp only [s, c] at *; omega
  have hB : natSetSpan B + 2 ≤ A.card + B.card := by dsimp only [s, c] at *; omega
  refine ⟨s - c, 2 * c - s, ?_, ?_⟩
  · omega
  · intro g hg
    have hgg := Finset.mem_Icc.mp hg
    obtain ⟨a, ha, b, hb, hab⟩ := dense_nat_sumset_interval A B (natSetSpan A) (natSetSpan B)
      (natSetSpan_upper A) (natSetSpan_upper B) hA hB g
      (by change s ≤ g + c; omega) (by change g ≤ c; omega)
    exact Finset.mem_add.mpr ⟨a, ha, b, hb, hab⟩

end Erdos345
