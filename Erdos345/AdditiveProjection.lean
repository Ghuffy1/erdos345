import Erdos345.IndexedSumset
import Erdos345.FiniteFiberBounds

namespace Erdos345

open scoped Pointwise

theorem image_indexed_sumset {ι M N : Type*} [DecidableEq ι]
    [AddCommMonoid M] [AddCommMonoid N] [DecidableEq M] [DecidableEq N]
    (I : Finset ι) (A : ι → Finset M) (f : M →+ N) :
    (∑ i ∈ I, A i).image f = ∑ i ∈ I, (A i).image f := by
  induction I using Finset.induction_on with
  | empty =>
    change ({0} : Finset M).image f = ({0} : Finset N)
    simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.image_add, ih]

theorem indexed_sumset_card_add {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (hA : ∀ i ∈ I, (A i).Nonempty) :
    (∑ i ∈ I, (A i).card) + 1 ≤ (∑ i ∈ I, A i).card + I.card := by
  have h := indexed_sumset_card_lower I A hA
  have heq : (∑ i ∈ I, (A i).card) = (∑ i ∈ I, ((A i).card - 1)) + I.card := by
    calc
      _ = ∑ i ∈ I, ((A i).card - 1 + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hp := Finset.card_pos.mpr (hA i hi)
        omega
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  omega

theorem sum_of_input_fibers_subset {ι G : Type*} [DecidableEq ι] [AddCommMonoid G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset ℕ) (f : ℕ →+ G) (b : ι → G) :
    (∑ i ∈ I, (A i).filter (fun n => f n = b i)) ⊆
      (∑ i ∈ I, A i).filter (fun n => f n = ∑ i ∈ I, b i) := by
  classical
  intro n hn
  obtain ⟨a, ha, rfl⟩ := (mem_indexed_sumset I (fun i => (A i).filter (fun n => f n = b i)) n).mp hn
  apply Finset.mem_filter.mpr
  constructor
  · exact (mem_indexed_sumset I A _).mpr ⟨a, (fun i hi => (Finset.mem_filter.mp (ha i hi)).1), rfl⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp (ha i hi)).2)

theorem sumset_fiber_card_bound {ι G : Type*} [DecidableEq ι] [AddCommMonoid G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset ℕ) (f : ℕ →+ G) (b : ι → G)
    (hb : ∀ i ∈ I, b i ∈ (A i).image f) :
    (∑ i ∈ I, ((A i).filter (fun n => f n = b i)).card) + 1 ≤
      ((∑ i ∈ I, A i).filter (fun n => f n = ∑ i ∈ I, b i)).card + I.card := by
  classical
  have hnon : ∀ i ∈ I, ((A i).filter (fun n => f n = b i)).Nonempty := by
    intro i hi
    obtain ⟨n, hn, hnb⟩ := Finset.mem_image.mp (hb i hi)
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hnb⟩⟩
  have hcard := Finset.card_le_card (sum_of_input_fibers_subset I A f b)
  exact (indexed_sumset_card_add I (fun i => (A i).filter (fun n => f n = b i)) hnon).trans
    (Nat.add_le_add_right hcard _)

end Erdos345
