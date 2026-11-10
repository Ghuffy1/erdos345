import Erdos345.ReserveRootBound
import Erdos345.DeletedPrefixEnergy

namespace Erdos345

def unreservedEndpoint (N k : ℕ) : ℕ := N - N / k

def unreservedPopulation (N k : ℕ) : Finset ℕ :=
  Finset.Icc 1 (unreservedEndpoint N k) \ Finset.Icc 2 257

theorem mem_unreservedPopulation (N k n : ℕ) :
    n ∈ unreservedPopulation N k ↔ n ≤ unreservedEndpoint N k ∧ (n = 1 ∨ 258 ≤ n) := by
  simp only [unreservedPopulation, Finset.mem_sdiff, Finset.mem_Icc]
  omega

theorem unreservedEndpoint_cast (N k : ℕ) :
    (unreservedEndpoint N k : ℝ) = (N : ℝ) - ((N / k : ℕ) : ℝ) := by
  exact Nat.cast_sub (Nat.div_le_self N k)

theorem unreservedEndpoint_ge_three_quarters (N k : ℕ) (hk : 4 ≤ k) :
    3 * (N : ℝ) / 4 ≤ unreservedEndpoint N k := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
  have hratio : (N : ℝ) / k ≤ (N : ℝ) / 4 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hkR
  rw [unreservedEndpoint_cast]
  linarith

theorem quarter_root_endpoint_le (N k : ℕ) (hk : 20 ≤ k) :
    (N : ℝ) * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ unreservedEndpoint N k := by
  have hroot := mul_le_mul_of_nonneg_left (quarter_root_le_one_sub_inv k hk) (Nat.cast_nonneg N)
  have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
  calc
    _ ≤ (N : ℝ) * (1 - (k : ℝ)⁻¹) := hroot
    _ = (N : ℝ) - (N : ℝ) / k := by ring
    _ ≤ (N : ℝ) - ((N / k : ℕ) : ℝ) := by linarith
    _ = _ := (unreservedEndpoint_cast N k).symm

theorem unreservedPopulation_contains_band (N k : ℕ) :
    Finset.Icc 258 (unreservedEndpoint N k) ⊆ unreservedPopulation N k := by
  intro n hn
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hn
  exact (mem_unreservedPopulation N k n).mpr ⟨hu, Or.inr hl⟩

theorem unreservedPopulation_nonempty (N k : ℕ) (hU : 1 ≤ unreservedEndpoint N k) :
    (unreservedPopulation N k).Nonempty :=
  ⟨1, (mem_unreservedPopulation N k 1).mpr ⟨hU, Or.inl rfl⟩⟩

/-- The prefix may lose zero and the 256 fixed auxiliary bases. Zero
is counted conservatively here even though its positive-power energy
vanishes. No reserved top base is charged when V <= U+1. -/
theorem unreservedPopulation_missing_le (N k V : ℕ) (hV : V ≤ unreservedEndpoint N k + 1) :
    ((Finset.range V) \ unreservedPopulation N k).card ≤ 257 := by
  have hsub : (Finset.range V) \ unreservedPopulation N k ⊆ (Finset.range 258).erase 1 := by
    intro n hn
    obtain ⟨hnV, hnR⟩ := Finset.mem_sdiff.mp hn
    have hnV' := Finset.mem_range.mp hnV
    rw [mem_unreservedPopulation] at hnR
    apply Finset.mem_erase.mpr
    constructor
    · omega
    · apply Finset.mem_range.mpr
      omega
  have hc := Finset.card_le_card hsub
  simpa using hc

end Erdos345
