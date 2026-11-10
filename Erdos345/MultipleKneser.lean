import Erdos345.CamKneser
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Tactic

namespace Erdos345

open scoped Pointwise

theorem group_sumset_nonempty {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset G) (hA : ∀ i ∈ I, (A i).Nonempty) :
    (∑ i ∈ I, A i).Nonempty := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (hA i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

theorem sumset_add_idempotent {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (hI : I.Nonempty) (A : ι → Finset G) (H : Finset G) (hH : H + H = H) :
    (∑ i ∈ I, (A i + H)) = (∑ i ∈ I, A i) + H := by
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert i I hi ih =>
    by_cases hempty : I = ∅
    · subst I
      simp
    · have hI' : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hI']
      calc
        A i + H + ((∑ j ∈ I, A j) + H) = (A i + ∑ j ∈ I, A j) + (H + H) := by ac_rfl
        _ = _ := by rw [hH]

theorem stabilizer_subset_group_sumset {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (hI : I.Nonempty) (A : ι → Finset G) (H : Finset G)
    (hA : ∀ i ∈ I, (A i).Nonempty) (hH : ∀ i ∈ I, H ⊆ (A i).addStab) :
    H ⊆ (∑ i ∈ I, A i).addStab := by
  obtain ⟨i, hi⟩ := hI
  rw [← Finset.add_sum_erase I A hi]
  exact (hH i hi).trans (Finset.subset_addStab_add_left
    (group_sumset_nonempty (I.erase i) A (fun j hj => hA j (Finset.mem_of_mem_erase hj))))

theorem multiple_kneser_fixed_stabilizer {ι G : Type*} [DecidableEq ι]
    [AddCommGroup G] [DecidableEq G] (I : Finset ι) (hI : I.Nonempty)
    (A : ι → Finset G) (H : Finset G)
    (hA : ∀ i ∈ I, (A i).Nonempty) (hH : ∀ i ∈ I, A i + H = A i)
    (hstab : (∑ i ∈ I, A i).addStab = H) :
    (∑ i ∈ I, (A i).card) + H.card ≤
      (∑ i ∈ I, A i).card + I.card * H.card := by
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert i I hi ih =>
    by_cases hempty : I = ∅
    · subst I
      simp
    · have hI' : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have hrest : ∀ j ∈ I, (A j).Nonempty := fun j hj => hA j (Finset.mem_insert_of_mem hj)
      have hAi := hA i (Finset.mem_insert_self _ _)
      have hprefix := group_sumset_nonempty I A hrest
      have hle : (∑ j ∈ I, A j).addStab ⊆ H := by
        rw [Finset.sum_insert hi] at hstab
        rw [← hstab, add_comm (A i)]
        exact Finset.subset_addStab_add_left hAi
      have hge : H ⊆ (∑ j ∈ I, A j).addStab := by
        apply stabilizer_subset_group_sumset I hI' A H hrest
        intro j hj
        apply (Finset.add_subset_left_iff (hrest j hj)).mp
        exact (hH j (Finset.mem_insert_of_mem hj)).le
      have hprefixstab : (∑ j ∈ I, A j).addStab = H := Finset.Subset.antisymm hle hge
      have hrec := ih hI' hrest (fun j hj => hH j (Finset.mem_insert_of_mem hj)) hprefixstab
      have hprefixH : (∑ j ∈ I, A j) + H = ∑ j ∈ I, A j := by
        rw [← hprefixstab, Finset.add_addStab]
      have hstep := Finset.add_kneser (A i) (∑ j ∈ I, A j)
      rw [Finset.sum_insert hi] at hstab
      rw [hstab, hH i (Finset.mem_insert_self _ _), hprefixH] at hstep
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
        Nat.add_mul, one_mul]
      omega

/-- Kneser's inequality for an arbitrary finite nonempty family, with
the stabilizer of its actual full sumset. -/
theorem multiple_kneser {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (hI : I.Nonempty) (A : ι → Finset G)
    (hA : ∀ i ∈ I, (A i).Nonempty) :
    let H := (∑ i ∈ I, A i).addStab
    (∑ i ∈ I, (A i + H).card) ≤ (∑ i ∈ I, A i).card + (I.card - 1) * H.card := by
  classical
  dsimp only
  let S := ∑ i ∈ I, A i
  let H := S.addStab
  have hS : S.Nonempty := group_sumset_nonempty I A hA
  have hH : H.Nonempty := hS.addStab
  have hidem : H + H = H := Finset.addStab_add_addStab S
  have hsum : (∑ i ∈ I, (A i + H)) = S := by
    rw [sumset_add_idempotent I hI A H hidem]
    exact Finset.add_addStab S
  have hfixed (i : ι) (_hi : i ∈ I) : (A i + H) + H = A i + H := by
    rw [add_assoc, hidem]
  have hbound := multiple_kneser_fixed_stabilizer I hI (fun i => A i + H) H
    (fun i hi => (hA i hi).add hH) hfixed (by rw [hsum])
  rw [hsum] at hbound
  have hcard : 0 < I.card := Finset.card_pos.mpr hI
  have heq : I.card = (I.card - 1) + 1 := by omega
  rw [heq, Nat.add_mul, one_mul] at hbound
  change (∑ i ∈ I, (A i + H).card) ≤ S.card + (I.card - 1) * H.card
  omega

end Erdos345
