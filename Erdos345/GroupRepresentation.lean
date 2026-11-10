import Erdos345.FinitePowerSums
import Erdos345.TailCompletion

namespace Erdos345

theorem finitePowerSums_le_span (G : Finset ℕ) (k m : ℕ)
    (hm : m ∈ finitePowerSums G k) : m ≤ ∑ n ∈ G, n ^ k := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
  exact Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp hS)

theorem finitePowerSums_subset_interval (G : Finset ℕ) (k l : ℕ)
    (hspan : (∑ n ∈ G, n ^ k) ≤ l) :
    finitePowerSums G k ⊆ Finset.Icc 0 l := by
  intro m hm
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le m, (finitePowerSums_le_span G k m hm).trans hspan⟩

/-- A sum of one subset-sum from each disjoint base group is itself a
sum of distinct powers with the same global base bound. -/
theorem representedUpTo_of_group_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Finset ℕ) (k N : ℕ) (hsub : ∀ i, H i ⊆ Finset.Icc 1 N)
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (a : ι → ℕ) (ha : ∀ i, a i ∈ finitePowerSums (H i) k) :
    representedUpTo k N (∑ i, a i) := by
  classical
  have hex : ∀ i, ∃ S : Finset ℕ, S ⊆ H i ∧ (∑ n ∈ S, n ^ k) = a i := by
    intro i
    obtain ⟨S, hS, heq⟩ := Finset.mem_image.mp (ha i)
    exact ⟨S, Finset.mem_powerset.mp hS, heq⟩
  choose S hS hsum using hex
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι) : Set ι) S := by
    intro i _ j _ hij
    exact (hdisj i j hij).mono (hS i) (hS j)
  refine ⟨Finset.univ.biUnion S, ?_, ?_⟩
  · intro n hn
    obtain ⟨i, _, hni⟩ := Finset.mem_biUnion.mp hn
    exact Finset.mem_Icc.mp (hsub i (hS i hni))
  · rw [Finset.sum_biUnion hpair]
    exact Finset.sum_congr rfl (fun i _ => hsum i)

end Erdos345
