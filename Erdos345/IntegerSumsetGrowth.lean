import Erdos345.PeriodicSumsetLifting
import Erdos345.QuotientNewClasses

namespace Erdos345

open scoped Classical Pointwise

/-- The integer growth estimate underlying Lev's theorem, stated with
the explicit residue-generation hypothesis of the last summand. -/
theorem integer_sumset_growth_of_generating {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (j : ι) (hj : j ∈ I)
    (hA : ∀ i ∈ I, (A i).Nonempty) (q : ℕ) (hq : 0 < q) [NeZero q]
    (hzero : 0 ∈ A j) (hendpoint : q ∈ A j)
    (hgen : AddSubgroup.closure (naturalResidueImage (A j) q : Set (ZMod q)) = ⊤) :
    (∑ i ∈ I.erase j, A i).card +
        min q ((∑ i ∈ I, (naturalResidueImage (A i) q).card) + 1 - I.card) ≤
      (∑ i ∈ I, A i).card := by
  classical
  let T := ∑ i ∈ I.erase j, A i
  let S := ∑ i ∈ I, A i
  let P := naturalResidueImage T q
  let R := naturalResidueImage S q
  let B := naturalResidueImage (A j) q
  have hsum : S = T + A j := by
    change (∑ i ∈ I, A i) = (∑ i ∈ I.erase j, A i) + A j
    rw [← Finset.add_sum_erase I A hj, add_comm]
  have hT : T ⊆ S := by
    rw [hsum]
    intro t ht
    exact Finset.mem_add.mpr ⟨t, ht, 0, hzero, add_zero t⟩
  have htrans : T.image (fun n => n + q) ⊆ S := by
    rw [hsum]
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_add.mpr ⟨t, ht, q, hendpoint, rfl⟩
  have hres : R = P + B := by
    change S.image (Nat.castAddMonoidHom (ZMod q)) =
      T.image (Nat.castAddMonoidHom (ZMod q)) + (A j).image (Nat.castAddMonoidHom (ZMod q))
    rw [hsum, Finset.image_add]
  have hP : P.Nonempty := Finset.image_nonempty.mpr
    (indexed_sumset_nonempty (I.erase j) A (fun i hi => hA i (Finset.mem_of_mem_erase hi)))
  have hR : R.Nonempty := Finset.image_nonempty.mpr (indexed_sumset_nonempty I A hA)
  have hglobal := endpoint_extension_card_growth T S q hq hT htrans
  by_cases hfull : R = Finset.univ
  · have hcard : R.card = q := by rw [hfull, Finset.card_univ, ZMod.card]
    change T.card + R.card ≤ S.card at hglobal
    rw [hcard] at hglobal
    exact (Nat.add_le_add_left (Nat.min_le_left _ _) T.card).trans hglobal
  · have hsat : P + R.addStab ⊆ R := by
      have hPR : P ⊆ R := Finset.image_subset_image hT
      calc
        P + R.addStab ⊆ R + R.addStab := Finset.add_subset_add hPR (Finset.Subset.refl _)
        _ = R := Finset.add_addStab R
    have hnew :
        let R' := naturalResidueImage S q
        let H := AddAction.stabilizer (ZMod q) (R' : Set (ZMod q))
        P.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H) ⊂
          R'.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H) := by
      dsimp only
      change P.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ AddAction.stabilizer (ZMod q) (R : Set (ZMod q))) ⊂
        R.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ AddAction.stabilizer (ZMod q) (R : Set (ZMod q)))
      rw [hres]
      apply quotient_new_class_of_generating P B hP
      · exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩
      · exact hgen
      · rwa [← hres]
    have hb := periodic_sumset_lifting I ⟨j, hj⟩ A hA T q hq hT htrans hsat hnew
    change T.card + (∑ i ∈ I, (naturalResidueImage (A i) q).card) + 1 ≤ S.card + I.card at hb
    have htcard : T.card ≤ S.card := Finset.card_le_card hT
    have hmin := Nat.min_le_right q ((∑ i ∈ I, (naturalResidueImage (A i) q).card) + 1 - I.card)
    change T.card + min q ((∑ i ∈ I, (naturalResidueImage (A i) q).card) + 1 - I.card) ≤ S.card
    omega

end Erdos345
