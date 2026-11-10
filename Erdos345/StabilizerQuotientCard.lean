import Erdos345.QuotientFiberBounds

namespace Erdos345

open scoped Classical Pointwise

theorem stabilizer_natCard {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (R : Finset G) (hR : R.Nonempty) :
    Nat.card (AddAction.stabilizer G (R : Set G)) = R.addStab.card := by
  have heq := Finset.coe_addStab hR
  have hc := Nat.card_congr (Set.equivOfEq heq)
  calc
    Nat.card (AddAction.stabilizer G (R : Set G)) = Nat.card R.addStab := hc.symm
    _ = R.addStab.card := Nat.card_eq_finsetCard _

theorem stabilizer_quotient_saturation_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (R S : Finset G) [DecidableEq (G ⧸ AddAction.stabilizer G (R : Set G))]
    (hR : R.Nonempty) :
    (S.image (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G))).card *
      Nat.card (AddAction.stabilizer G (R : Set G)) = (S + R.addStab).card := by
  rw [stabilizer_natCard R hR, Nat.mul_comm]
  convert Finset.card_addStab_add_card_image_coe' S R using 1

theorem stabilizer_quotient_self_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (R : Finset G) [DecidableEq (G ⧸ AddAction.stabilizer G (R : Set G))]
    (hR : R.Nonempty) :
    R.card = (R.image (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G))).card *
      Nat.card (AddAction.stabilizer G (R : Set G)) := by
  simpa only [Finset.add_addStab] using (stabilizer_quotient_saturation_card R R hR).symm

theorem stabilizer_quotient_mem_image {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (R S : Finset G) [DecidableEq (G ⧸ AddAction.stabilizer G (R : Set G))]
    (hR : R.Nonempty) (g : G) :
    QuotientAddGroup.mk g ∈
        S.image (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G)) ↔
      g ∈ S + R.addStab := by
  classical
  constructor
  · intro hg
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hg
    change (QuotientAddGroup.mk' (AddAction.stabilizer G (R : Set G))) s =
      (QuotientAddGroup.mk' (AddAction.stabilizer G (R : Set G))) g at heq
    obtain ⟨z, hz, hsz⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp heq
    have hz' : z ∈ R.addStab := by
      change z ∈ (R.addStab : Set G)
      rw [Finset.coe_addStab hR]
      exact hz
    exact Finset.mem_add.mpr ⟨s, hs, z, hz', hsz⟩
  · intro hg
    obtain ⟨s, hs, z, hz, rfl⟩ := Finset.mem_add.mp hg
    apply Finset.mem_image.mpr
    refine ⟨s, hs, ?_⟩
    change (QuotientAddGroup.mk' (AddAction.stabilizer G (R : Set G))) s =
      (QuotientAddGroup.mk' (AddAction.stabilizer G (R : Set G))) (s + z)
    apply (QuotientAddGroup.mk'_eq_mk' _).mpr
    refine ⟨z, ?_, rfl⟩
    change z ∈ (AddAction.stabilizer G (R : Set G) : Set G)
    rw [← Finset.coe_addStab hR]
    exact hz

end Erdos345
