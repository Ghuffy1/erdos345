import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Erdos345

/-- A uniform supply of at least the total number of requested elements
allows disjoint choices from all the candidate sets. -/
theorem exists_disjoint_subsets_of_uniform_card {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (F : ι → Finset α) (s : ℕ)
    (hF : ∀ i, Fintype.card ι * s ≤ (F i).card) :
    ∃ B : ι → Finset α, (∀ i, B i ⊆ F i) ∧ (∀ i, (B i).card = s) ∧
      ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
  classical
  let T : ι × Fin s → Finset α := fun x => F x.1
  have hhall : ∀ A : Finset (ι × Fin s), A.card ≤ (A.biUnion T).card := by
    intro A
    by_cases hA : A.Nonempty
    · obtain ⟨x, hx⟩ := hA
      calc
        A.card ≤ Fintype.card (ι × Fin s) := Finset.card_le_univ A
        _ = Fintype.card ι * s := by simp
        _ ≤ (F x.1).card := hF x.1
        _ ≤ (A.biUnion T).card := Finset.card_le_card (by
          intro a ha
          exact Finset.mem_biUnion.mpr ⟨x, hx, ha⟩)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hA, Finset.card_empty,
        Finset.biUnion_empty]
      exact Nat.zero_le _
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hhall
  let B : ι → Finset α := fun i => Finset.univ.image (fun t : Fin s => f (i, t))
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i a ha
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    exact hmem (i, t)
  · intro i
    have hinj : Function.Injective (fun t : Fin s => f (i, t)) := by
      intro t u htu
      exact congrArg Prod.snd (hf htu)
    change (Finset.univ.image (fun t : Fin s => f (i, t))).card = s
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hai
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp haj
    exact hij (congrArg Prod.fst (hf (ht.trans hu.symm)))

end Erdos345
