import Erdos345.PhaseWindowEnergy

namespace Erdos345

/-- Different integer phase bands cannot share a base. -/
theorem phaseWindows_pairwise_disjoint (J : Finset ℕ) (f : ℕ → ℝ)
    (a b : ℕ → ℝ) (z : ℕ → ℤ) (hz : Set.InjOn z (J : Set ℕ))
    (hphase : ∀ j ∈ J, ∀ n ∈ naturalWindow (a j) (b j),
      (z j : ℝ) + 1 / 8 ≤ f n ∧ f n ≤ (z j : ℝ) + 1 / 4) :
    (J : Set ℕ).PairwiseDisjoint (fun j => naturalWindow (a j) (b j)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hiB := hphase i hi n hni
  have hjB := hphase j hj n hnj
  have hne : z i ≠ z j := fun he => hij (hz hi hj he)
  have hsep : z i + 1 ≤ z j ∨ z j + 1 ≤ z i := by omega
  rcases hsep with hsep | hsep
  · have hR : (z i : ℝ) + 1 ≤ z j := by exact_mod_cast hsep
    linarith
  · have hR : (z j : ℝ) + 1 ≤ z i := by exact_mod_cast hsep
    linarith

/-- Sum the contributions of finitely many separated phase windows.
The interval lengths and membership in the actual population stay
explicit, so this lemma cannot silently discard reserved bases. -/
theorem stacked_naturalWindow_energy_lower (R J : Finset ℕ) (f : ℕ → ℝ)
    (a b : ℕ → ℝ) (z : ℕ → ℤ) (hz : Set.InjOn z (J : Set ℕ))
    (ha : ∀ j ∈ J, 0 ≤ a j) (hlen : ∀ j ∈ J, 2 ≤ b j - a j)
    (hsub : ∀ j ∈ J, naturalWindow (a j) (b j) ⊆ R)
    (hphase : ∀ j ∈ J, ∀ n ∈ naturalWindow (a j) (b j),
      (z j : ℝ) + 1 / 8 ≤ f n ∧ f n ≤ (z j : ℝ) + 1 / 4) :
    (∑ j ∈ J, (b j - a j)) / 32 ≤ finiteSineEnergy R f := by
  have hdisj := phaseWindows_pairwise_disjoint J f a b z hz hphase
  have hsum : (∑ j ∈ J, finiteSineEnergy (naturalWindow (a j) (b j)) f) =
      finiteSineEnergy (J.biUnion (fun j => naturalWindow (a j) (b j))) f := by
    unfold finiteSineEnergy
    rw [Finset.sum_biUnion hdisj]
  have hu : J.biUnion (fun j => naturalWindow (a j) (b j)) ⊆ R := by
    intro n hn
    obtain ⟨j, hj, hnj⟩ := Finset.mem_biUnion.mp hn
    exact hsub j hj hnj
  calc
    _ = ∑ j ∈ J, (b j - a j) / 32 := by rw [Finset.sum_div]
    _ ≤ ∑ j ∈ J, finiteSineEnergy (naturalWindow (a j) (b j)) f :=
      Finset.sum_le_sum (fun j hj => naturalWindow_energy_lower _ f (a j) (b j)
        (ha j hj) (hlen j hj) (fun _ h => h) (z j) (hphase j hj))
    _ = _ := hsum
    _ ≤ _ := finiteSineEnergy_mono _ R hu f

end Erdos345
