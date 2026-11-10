import Erdos345.FiniteFiberBounds
import Erdos345.MultipleKneser
import Mathlib.GroupTheory.Coset.Card

namespace Erdos345

open scoped Classical Pointwise

theorem quotient_full_fiber_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (c : G ⧸ H) :
    ((Finset.univ : Finset G).filter (fun a => QuotientAddGroup.mk a = c)).card = Nat.card H := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet H ({c} : Set (G ⧸ H)))
  simpa only [Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Fintype.card_prod,
    Fintype.card_unique, mul_one, Fintype.card_subtype] using h

theorem quotient_fiber_card_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (S : Finset G) (c : G ⧸ H) :
    (S.filter (fun a => QuotientAddGroup.mk a = c)).card ≤ Nat.card H := by
  classical
  rw [← quotient_full_fiber_card H c]
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.subset_univ _)

theorem quotient_fiber_defect_bound {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (S : Finset G) (c : G ⧸ H)
    (hc : c ∈ S.image QuotientAddGroup.mk) :
    S.card + Nat.card H ≤ (S.filter (fun a => QuotientAddGroup.mk a = c)).card +
      (S.image (QuotientAddGroup.mk : G → G ⧸ H)).card * Nat.card H :=
  fiber_card_defect_bound S (QuotientAddGroup.mk : G → G ⧸ H) c (Nat.card H)
    hc (fun b _ => quotient_fiber_card_le H S b)

end Erdos345
