import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic

namespace Erdos345

open scoped Pointwise

theorem mem_indexed_sumset {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (m : ℕ) :
    m ∈ ∑ i ∈ I, A i ↔
      ∃ f : ι → ℕ, (∀ i ∈ I, f i ∈ A i) ∧ ∑ i ∈ I, f i = m := by
  change m ∈ ((∑ i ∈ I, A i : Finset ℕ) : Set ℕ) ↔ _
  rw [Finset.coe_sum, Set.mem_finsetSum]
  constructor
  · rintro ⟨f, hf, hsum⟩
    exact ⟨f, fun i hi => hf hi, hsum⟩
  · rintro ⟨f, hf, hsum⟩
    exact ⟨f, fun hi => hf _ hi, hsum⟩

theorem indexed_sumset_nonempty {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (hA : ∀ i ∈ I, (A i).Nonempty) :
    (∑ i ∈ I, A i).Nonempty := by
  classical
  have hex : ∀ i, ∃ a : ℕ, i ∈ I → a ∈ A i := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨a, ha⟩ := hA i hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose f hf using hex
  exact ⟨∑ i ∈ I, f i, (mem_indexed_sumset I A _).mpr ⟨f, hf, rfl⟩⟩

theorem indexed_sumset_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (L : ι → ℕ)
    (hA : ∀ i ∈ I, A i ⊆ Finset.Icc 0 (L i)) :
    (∑ i ∈ I, A i) ⊆ Finset.Icc 0 (∑ i ∈ I, L i) := by
  intro m hm
  obtain ⟨f, hf, rfl⟩ := (mem_indexed_sumset I A m).mp hm
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.zero_le _, Finset.sum_le_sum (fun i hi => (Finset.mem_Icc.mp (hA i hi (hf i hi))).2)⟩

theorem indexed_sumset_card_lower {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (hA : ∀ i ∈ I, (A i).Nonempty) :
    (∑ i ∈ I, ((A i).card - 1)) + 1 ≤ (∑ i ∈ I, A i).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hrest : ∀ j ∈ I, (A j).Nonempty := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hI := indexed_sumset_nonempty I A hrest
    have hstep := cauchy_davenport_add_of_linearOrder_isCancelAdd hAi hI
    have hrec := ih hrest
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hpos := Finset.card_pos.mpr hAi
    omega

end Erdos345
