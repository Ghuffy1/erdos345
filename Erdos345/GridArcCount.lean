import Erdos345.FlatInverseRadius
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max

namespace Erdos345

noncomputable def gridNear (q : ℕ) (c r : ℝ) : Finset ℕ :=
  (Finset.range q).filter (fun h => |(h : ℝ) / q - c| ≤ r)

theorem mem_gridNear (q h : ℕ) (c r : ℝ) :
    h ∈ gridNear q c r ↔ h < q ∧ |(h : ℝ) / q - c| ≤ r := by
  classical
  simp only [gridNear, Finset.mem_filter, Finset.mem_range]

/-- An interval of radius r contains at most ceil(2qr)+1 points of the
q-grid. No separation assumption about other intervals is required. -/
theorem card_gridNear_le (q : ℕ) (hq : 0 < q) (c r : ℝ) :
    (gridNear q c r).card ≤ ⌈2 * (q : ℝ) * r⌉₊ + 1 := by
  classical
  let s := gridNear q c r
  change s.card ≤ _
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.min'_le_max' hs
    have hsub : s ⊆ Finset.Icc a b := by
      intro h hh
      exact Finset.mem_Icc.mpr ⟨s.min'_le h hh, s.le_max' h hh⟩
    have hc : s.card ≤ b + 1 - a := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hal := (abs_le.mp ((mem_gridNear q a c r).mp ha).2).1
    have hbu := (abs_le.mp ((mem_gridNear q b c r).mp hb).2).2
    have hal' : (c - r) * q ≤ (a : ℝ) :=
      (le_div_iff₀ hqR).mp (by linarith)
    have hbu' : (b : ℝ) ≤ (c + r) * q :=
      (div_le_iff₀ hqR).mp (by linarith)
    have hspan : (b : ℝ) - a ≤ 2 * q * r := by nlinarith
    have hceil : 2 * (q : ℝ) * r ≤ (⌈2 * (q : ℝ) * r⌉₊ : ℝ) := Nat.le_ceil _
    have hspan' : ((b - a : ℕ) : ℝ) ≤ (⌈2 * (q : ℝ) * r⌉₊ : ℝ) := by
      rw [Nat.cast_sub hab]
      exact hspan.trans hceil
    have hnat : b - a ≤ ⌈2 * (q : ℝ) * r⌉₊ := by exact_mod_cast hspan'
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty, Nat.zero_le]

def centerNumerators (B : ℕ) : Finset ℤ := Finset.Icc (-(B : ℤ)) (2 * (B : ℤ))

theorem card_centerNumerators (B : ℕ) : (centerNumerators B).card = 3 * B + 1 := by
  simp only [centerNumerators, Int.card_Icc]
  have h : 2 * (B : ℤ) + 1 - -(B : ℤ) = (3 * B + 1 : ℕ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

noncomputable def commonRationalArcs (q B : ℕ) (r : ℝ) : Finset ℕ :=
  (centerNumerators B).biUnion (fun u => gridNear q ((u : ℝ) / B) r)

theorem card_commonRationalArcs_le (q B : ℕ) (hq : 0 < q) (r : ℝ) :
    (commonRationalArcs q B r).card ≤ (3 * B + 1) * (⌈2 * (q : ℝ) * r⌉₊ + 1) := by
  classical
  calc
    _ ≤ ∑ u ∈ centerNumerators B, (gridNear q ((u : ℝ) / B) r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ centerNumerators B, (⌈2 * (q : ℝ) * r⌉₊ + 1) :=
      Finset.sum_le_sum (fun u _ => card_gridNear_le q hq ((u : ℝ) / B) r)
    _ = _ := by simp [Finset.sum_const, card_centerNumerators]

/-- For a grid point in [0,1), radius at most one restricts the integer
numerator to the finite range [-B,2B]. -/
theorem mem_commonRationalArcs_of_near (q B h : ℕ) (hq : 0 < q) (hB : 0 < B)
    (hh : h < q) (r : ℝ) (hr : r ≤ 1) (u : ℤ)
    (hnear : |(h : ℝ) / q - (u : ℝ) / B| ≤ r) :
    h ∈ commonRationalArcs q B r := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hhR : (h : ℝ) < q := by exact_mod_cast hh
  have hα0 : 0 ≤ (h : ℝ) / q := by positivity
  have hα1 : (h : ℝ) / q < 1 := (div_lt_one hqR).mpr hhR
  have hbounds := abs_le.mp hnear
  have hul : -(B : ℝ) ≤ (u : ℝ) := by
    have hu : (-1 : ℝ) ≤ (u : ℝ) / B := by linarith
    have hu' := (le_div_iff₀ hBR).mp hu
    nlinarith
  have huu : (u : ℝ) ≤ 2 * B := by
    have hu : (u : ℝ) / B ≤ 2 := by linarith
    exact (div_le_iff₀ hBR).mp hu
  have humem : u ∈ centerNumerators B := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hul
    · exact_mod_cast huu
  apply Finset.mem_biUnion.mpr
  exact ⟨u, humem, (mem_gridNear q h ((u : ℝ) / B) r).mpr ⟨hh, hnear⟩⟩

end Erdos345
