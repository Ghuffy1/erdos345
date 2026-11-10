import Erdos345.SortedBlocksInterval
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos345

open scoped Classical Pointwise

/-- A sufficient interval theorem for the actual 128-set construction.
The stronger ratio margin avoids needing Lev's sharp density threshold. -/
theorem interval_for_128_sets (A : Fin 128 → Finset ℕ) (n l : ℕ) (hn : 2 ≤ n)
    (hcard : ∀ i, n ≤ (A i).card) (hzero : ∀ i, 0 ∈ A i)
    (hprimitive : ∀ i, ∀ d a : ℕ, (∀ v ∈ A i, v % d = a % d) → d = 1)
    (hbound : ∀ i, A i ⊆ Finset.Icc 0 l) (hl : l ≤ 33 * (n - 2) + 1) :
    ∃ a L : ℕ, 128 * (n - 1) ≤ L ∧
      ∀ g ∈ Finset.Icc a (a + L), g ∈ ∑ i, A i := by
  classical
  let f := fun i : Fin 128 => natSetSpan (A i)
  let σ := Tuple.sort f
  let D := fun i : ℕ => A (σ (Fin.ofNat 128 i))
  have hsort : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hmono : ∀ i j, i ≤ j → j < 128 → natSetSpan (D i) ≤ natSetSpan (D j) := by
    intro i j hij hj
    have hi : i < 128 := by omega
    apply hsort
    change i % 128 ≤ j % 128
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    exact hij
  have hupper : ∀ i < 128, natSetSpan (D i) ≤ l := by
    intro i _
    exact natSetSpan_le_of_bound (hbound _)
  obtain ⟨a, L, hL, hI⟩ := sorted_128_sumset_interval D n l hn
    (fun i _ => hcard _) (fun i _ => hzero _) (fun i _ => hprimitive _)
    hmono hupper hl
  have hsum : (∑ i ∈ Finset.range 128, D i) = ∑ i, A i := by
    calc
      _ = ∑ i : Fin 128, D i.val := (Fin.sum_univ_eq_sum_range D 128).symm
      _ = ∑ i : Fin 128, A (σ i) := by simp only [D, Fin.ofNat_val_eq_self]
      _ = _ := Equiv.sum_comp σ A
  refine ⟨a, L, hL, ?_⟩
  intro g hg
  rw [← hsum]
  exact hI g hg

end Erdos345
