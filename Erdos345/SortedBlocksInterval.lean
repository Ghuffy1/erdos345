import Erdos345.SortedPrefixDensity
import Erdos345.AlternatingSums
import Erdos345.DenseBalancedInterval

namespace Erdos345

open scoped Classical Pointwise

theorem sorted_128_sumset_interval (A : ℕ → Finset ℕ) (n l : ℕ) (hn : 2 ≤ n)
    (hcard : ∀ i < 128, n ≤ (A i).card)
    (hzero : ∀ i < 128, 0 ∈ A i)
    (hprimitive : ∀ i < 128, ∀ d a : ℕ, (∀ v ∈ A i, v % d = a % d) → d = 1)
    (hmono : ∀ i j, i ≤ j → j < 128 → natSetSpan (A i) ≤ natSetSpan (A j))
    (hupper : ∀ i < 128, natSetSpan (A i) ≤ l)
    (hl : l ≤ 33 * (n - 2) + 1) :
    ∃ a L : ℕ, 128 * (n - 1) ≤ L ∧
      ∀ g ∈ Finset.Icc a (a + L), g ∈ ∑ i ∈ Finset.range 128, A i := by
  let E := fun i => A (2 * i)
  let O := fun i => A (2 * i + 1)
  let S₀ := ∑ i ∈ Finset.range 64, E i
  let S₁ := ∑ i ∈ Finset.range 64, O i
  have he : natSetSpan S₀ + 64 * (n - 1) + 2 ≤ 2 * S₀.card := by
    apply sorted_prefix_density E 32 n hn
    · intro i hi
      exact hcard _ (by omega)
    · intro i hi
      exact hzero _ (by omega)
    · intro i hi
      exact hprimitive _ (by omega)
    · intro i j hij hj
      exact hmono _ _ (by omega) (by omega)
    · intro i hi
      exact (hupper _ (by omega)).trans hl
  have ho : natSetSpan S₁ + 64 * (n - 1) + 2 ≤ 2 * S₁.card := by
    apply sorted_prefix_density O 32 n hn
    · intro i hi
      exact hcard _ (by omega)
    · intro i hi
      exact hzero _ (by omega)
    · intro i hi
      exact hprimitive _ (by omega)
    · intro i j hij hj
      exact hmono _ _ (by omega) (by omega)
    · intro i hi
      exact (hupper _ (by omega)).trans hl
  have hbalance : natSetSpan S₀ ≤ natSetSpan S₁ ∧ natSetSpan S₁ ≤ natSetSpan S₀ + l := by
    have hnE : ∀ i ∈ Finset.range 64, (E i).Nonempty :=
      fun i hi => ⟨0, hzero _ (by have := Finset.mem_range.mp hi; omega)⟩
    have hnO : ∀ i ∈ Finset.range 64, (O i).Nonempty :=
      fun i hi => ⟨0, hzero _ (by have := Finset.mem_range.mp hi; omega)⟩
    rw [indexed_sumset_span (Finset.range 64) E hnE, indexed_sumset_span (Finset.range 64) O hnO]
    exact alternating_span_balance (fun i => natSetSpan (A i)) 64 l hmono hupper
  have hl' : l ≤ 2 * (64 * (n - 1)) := by omega
  obtain ⟨a, L, hL, hI⟩ := interval_of_dense_balanced_sumsets S₀ S₁ l (64 * (n - 1)) he ho hbalance hl'
  refine ⟨a, L, by omega, ?_⟩
  intro g hg
  rw [show 128 = 2 * 64 by norm_num, sum_range_even_odd]
  exact hI g hg

end Erdos345
