import Erdos345.DisjointAllocation
import Erdos345.ReservedGroupSelection

namespace Erdos345

def reserveGroupSize (N k : ℕ) : ℕ := N / (512 * k)

/-- The good-reserve count has enough slack for disjoint allocations to
all 128 groups. Every allocated base retains its own residue-support bound. -/
theorem reserved_good_allocation (N k : ℕ) (G : Fin 128 → Finset ℕ)
    (hgood : ∀ j, (reserveCount N k : ℝ) / 2 ≤
      (((reservedBases N k).filter (fun c =>
        ((c ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues (G j) k (c ^ k)).card)).card : ℝ)) :
    ∃ B : Fin 128 → Finset ℕ,
      (∀ j, B j ⊆ reservedBases N k) ∧
      (∀ j, (B j).card = reserveGroupSize N k) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ j c, c ∈ B j →
        ((c ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues (G j) k (c ^ k)).card := by
  classical
  let F := fun j : Fin 128 => (reservedBases N k).filter (fun c =>
    ((c ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues (G j) k (c ^ k)).card)
  have hF : ∀ j, Fintype.card (Fin 128) * reserveGroupSize N k ≤ (F j).card := by
    intro j
    have h := hgood j
    change (reserveCount N k : ℝ) / 2 ≤ ((F j).card : ℝ) at h
    have hR : (reserveCount N k : ℝ) ≤ 2 * ((F j).card : ℝ) := by linarith
    have hN : reserveCount N k ≤ 2 * (F j).card := by exact_mod_cast hR
    simp only [Fintype.card_fin, reserveCount, reserveGroupSize] at *
    omega
  obtain ⟨B, hsub, hcard, hdisj⟩ :=
    exists_disjoint_subsets_of_uniform_card F (reserveGroupSize N k) hF
  refine ⟨B, ?_, hcard, hdisj, ?_⟩
  · intro j c hc
    exact (Finset.mem_filter.mp (hsub j hc)).1
  · intro j c hc
    exact (Finset.mem_filter.mp (hsub j hc)).2

end Erdos345
