import Erdos345.SortedPrefixGrowth

namespace Erdos345

open scoped Classical Pointwise

/-- A paired estimate sufficient for the 64-summand blocks used here.
The upper half of the growth terms is saturated. -/
theorem paired_span_min_bound (L : ℕ → ℕ) (h n : ℕ) (hn : 2 ≤ n)
    (hlower : ∀ i < 2 * h, n - 1 ≤ L i)
    (hupper : ∀ i < 2 * h, L i ≤ (h + 1) * (n - 2) + 1)
    (hpair : ∀ i < h, L i ≤ L (h + i)) :
    (∑ i ∈ Finset.range (2 * h), L i) + 2 * h * (n - 1) ≤
      2 * ∑ i ∈ Finset.range (2 * h), min (L i) ((i + 1) * (n - 2) + 1) := by
  let M := fun i => min (L i) ((i + 1) * (n - 2) + 1)
  have hlow : h * (n - 1) ≤ ∑ i ∈ Finset.range h, M i := by
    calc
      h * (n - 1) = ∑ _i ∈ Finset.range h, (n - 1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hLi := hlower i (by omega)
        have hm : n - 1 ≤ (i + 1) * (n - 2) + 1 := by
          have heq : n - 1 = (n - 2) + 1 := by omega
          nlinarith [Nat.zero_le (i * (n - 2))]
        exact le_min hLi hm
  have hsat : (∑ i ∈ Finset.range h, M (h + i)) = ∑ i ∈ Finset.range h, L (h + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hLi := hupper (h + i) (by omega)
    have hm : (h + 1) * (n - 2) ≤ (h + i + 1) * (n - 2) := by
      nlinarith [Nat.zero_le (i * (n - 2))]
    exact min_eq_left (hLi.trans (Nat.add_le_add_right hm 1))
  have hpairs : (∑ i ∈ Finset.range h, L i) ≤ ∑ i ∈ Finset.range h, L (h + i) :=
    Finset.sum_le_sum (fun i hi => hpair i (Finset.mem_range.mp hi))
  change (∑ i ∈ Finset.range (2 * h), L i) + 2 * h * (n - 1) ≤
    2 * ∑ i ∈ Finset.range (2 * h), M i
  rw [show 2 * h = h + h by omega, Finset.sum_range_add, Finset.sum_range_add, hsat]
  nlinarith

theorem sorted_prefix_density (A : ℕ → Finset ℕ) (h n : ℕ) (hn : 2 ≤ n)
    (hcard : ∀ i < 2 * h, n ≤ (A i).card)
    (hzero : ∀ i < 2 * h, 0 ∈ A i)
    (hprimitive : ∀ i < 2 * h, ∀ d a : ℕ, (∀ v ∈ A i, v % d = a % d) → d = 1)
    (hmono : ∀ i l, i ≤ l → l < 2 * h → natSetSpan (A i) ≤ natSetSpan (A l))
    (hupper : ∀ i < 2 * h, natSetSpan (A i) ≤ (h + 1) * (n - 2) + 1) :
    natSetSpan (∑ i ∈ Finset.range (2 * h), A i) + 2 * h * (n - 1) + 2 ≤
      2 * (∑ i ∈ Finset.range (2 * h), A i).card := by
  have hnon : ∀ i ∈ Finset.range (2 * h), (A i).Nonempty :=
    fun i hi => ⟨0, hzero i (Finset.mem_range.mp hi)⟩
  have hg := sorted_prefix_card_lower A (2 * h) n hn hcard hzero hprimitive hmono
  have hp := paired_span_min_bound (fun i => natSetSpan (A i)) h n hn
    (fun i hi => by
      have hc := hcard i hi
      have hs := card_le_natSetSpan_add_one (A i)
      omega) hupper (fun i hi => hmono i (h + i) (by omega) (by omega))
  rw [indexed_sumset_span (Finset.range (2 * h)) A hnon]
  nlinarith

end Erdos345
