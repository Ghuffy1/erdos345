import Erdos345.IndexedSumset
import Mathlib.Data.Finset.Lattice.Fold

namespace Erdos345

open scoped Pointwise

def natSetSpan (A : Finset ℕ) : ℕ := A.sup id

theorem le_natSetSpan {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) : a ≤ natSetSpan A :=
  Finset.le_sup (f := id) ha

theorem natSetSpan_mem {A : Finset ℕ} (hA : A.Nonempty) : natSetSpan A ∈ A := by
  simpa only [natSetSpan, Set.image_id, Finset.mem_coe] using
    (Finset.sup_mem_of_nonempty (f := id) hA)

theorem natSetSpan_upper (A : Finset ℕ) : A ⊆ Finset.Icc 0 (natSetSpan A) := by
  intro a ha
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, le_natSetSpan ha⟩

theorem natSetSpan_le_of_bound {A : Finset ℕ} {L : ℕ} (hA : A ⊆ Finset.Icc 0 L) :
    natSetSpan A ≤ L := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.mem_Icc.mp (hA ha)).2

theorem indexed_sumset_span {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (A : ι → Finset ℕ) (hA : ∀ i ∈ I, (A i).Nonempty) :
    natSetSpan (∑ i ∈ I, A i) = ∑ i ∈ I, natSetSpan (A i) := by
  apply le_antisymm
  · exact natSetSpan_le_of_bound (indexed_sumset_bound I A (fun i => natSetSpan (A i))
      (fun i _ => natSetSpan_upper (A i)))
  · apply le_natSetSpan
    exact (mem_indexed_sumset I A _).mpr
      ⟨fun i => natSetSpan (A i), (fun i hi => natSetSpan_mem (hA i hi)), rfl⟩

theorem indexed_sumset_zero {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (A : ι → Finset ℕ) (hA : ∀ i ∈ I, 0 ∈ A i) : 0 ∈ ∑ i ∈ I, A i := by
  apply (mem_indexed_sumset I A 0).mpr
  exact ⟨fun _ => 0, hA, by simp⟩

theorem card_le_natSetSpan_add_one (A : Finset ℕ) : A.card ≤ natSetSpan A + 1 := by
  have h := Finset.card_le_card (natSetSpan_upper A)
  simpa using h

end Erdos345
