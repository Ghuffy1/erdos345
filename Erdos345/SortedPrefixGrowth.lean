import Erdos345.LevIntegerGrowth
import Erdos345.FiniteSumsetSpan

namespace Erdos345

open scoped Classical Pointwise

theorem sorted_prefix_growth_step (A : ℕ → Finset ℕ) (k n j : ℕ)
    (hn : 2 ≤ n) (hj : j < k)
    (hcard : ∀ i < k, n ≤ (A i).card)
    (hzero : ∀ i < k, 0 ∈ A i)
    (hprimitive : ∀ i < k, ∀ d a : ℕ, (∀ v ∈ A i, v % d = a % d) → d = 1)
    (hmono : ∀ i l, i ≤ l → l < k → natSetSpan (A i) ≤ natSetSpan (A l)) :
    (∑ i ∈ Finset.range j, A i).card +
        min (natSetSpan (A j)) ((j + 1) * (n - 2) + 1) ≤
      (∑ i ∈ Finset.range (j + 1), A i).card := by
  have hAj : (A j).Nonempty := ⟨0, hzero j hj⟩
  have hq : 0 < natSetSpan (A j) := by
    have hc := card_le_natSetSpan_add_one (A j)
    have hcn := hcard j hj
    omega
  let _ : NeZero (natSetSpan (A j)) := ⟨by omega⟩
  have hb := lev_uniform_growth (Finset.range (j + 1)) A j (by simp)
    (natSetSpan (A j)) n hq hn
    (fun i hi => hcard i (by have := Finset.mem_range.mp hi; omega))
    (fun i hi => by
      intro v hv
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
        (le_natSetSpan hv).trans (hmono i j (by have := Finset.mem_range.mp hi; omega) hj)⟩)
    (hzero j hj) (natSetSpan_mem hAj) (hprimitive j hj)
  have herase : (Finset.range (j + 1)).erase j = Finset.range j := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  simpa only [Finset.card_range, herase] using hb

/-- Accumulating Lev's growth estimate along a family ordered by span. -/
theorem sorted_prefix_card_lower (A : ℕ → Finset ℕ) (k n : ℕ)
    (hn : 2 ≤ n)
    (hcard : ∀ i < k, n ≤ (A i).card)
    (hzero : ∀ i < k, 0 ∈ A i)
    (hprimitive : ∀ i < k, ∀ d a : ℕ, (∀ v ∈ A i, v % d = a % d) → d = 1)
    (hmono : ∀ i l, i ≤ l → l < k → natSetSpan (A i) ≤ natSetSpan (A l)) :
    1 + (∑ j ∈ Finset.range k, min (natSetSpan (A j)) ((j + 1) * (n - 2) + 1)) ≤
      (∑ i ∈ Finset.range k, A i).card := by
  have hprefix : ∀ l ≤ k,
      1 + (∑ j ∈ Finset.range l, min (natSetSpan (A j)) ((j + 1) * (n - 2) + 1)) ≤
        (∑ i ∈ Finset.range l, A i).card := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      have hstep := sorted_prefix_growth_step A k n l hn (by omega) hcard hzero hprimitive hmono
      rw [Finset.sum_range_succ]
      omega
  exact hprefix k le_rfl

end Erdos345
