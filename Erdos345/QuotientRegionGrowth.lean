import Erdos345.EndpointSumsetGrowth
import Erdos345.StabilizerQuotientCard
import Erdos345.FiniteFiberPartition

namespace Erdos345

open scoped Classical Pointwise

theorem quotient_region_residue_image (S T : Finset ℕ) (q : ℕ) [NeZero q]
    (hR : (naturalResidueImage S q).Nonempty)
    (hsat : naturalResidueImage T q + (naturalResidueImage S q).addStab ⊆
      naturalResidueImage S q) :
    let R := naturalResidueImage S q
    let P := naturalResidueImage T q
    let H := AddAction.stabilizer (ZMod q) (R : Set (ZMod q))
    let U := S.filter (fun n : ℕ => QuotientAddGroup.mk (n : ZMod q) ∈
      P.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H))
    naturalResidueImage U q = P + R.addStab := by
  dsimp only
  rw [naturalResidueImage, image_filter_mem_preimage]
  ext r
  simp only [Finset.mem_filter]
  rw [stabilizer_quotient_mem_image _ _ hR]
  exact ⟨fun h => h.2, fun h => ⟨hsat h, h⟩⟩

theorem quotient_old_region_growth (S T : Finset ℕ) (q : ℕ) (hq : 0 < q) [NeZero q]
    (hR : (naturalResidueImage S q).Nonempty)
    (hT : T ⊆ S) (htrans : T.image (fun n => n + q) ⊆ S)
    (hsat : naturalResidueImage T q + (naturalResidueImage S q).addStab ⊆
      naturalResidueImage S q) :
    let R := naturalResidueImage S q
    let P := naturalResidueImage T q
    let H := AddAction.stabilizer (ZMod q) (R : Set (ZMod q))
    T.card + (P + R.addStab).card ≤
      (S.filter (fun n : ℕ => QuotientAddGroup.mk (n : ZMod q) ∈
        P.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H))).card := by
  dsimp only
  let R := naturalResidueImage S q
  let P := naturalResidueImage T q
  let H := AddAction.stabilizer (ZMod q) (R : Set (ZMod q))
  let U := S.filter (fun n : ℕ => QuotientAddGroup.mk (n : ZMod q) ∈
    P.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H))
  have hTU : T ⊆ U := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hT hn,
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hn)⟩
  have htranslate : T.image (fun n => n + q) ⊆ U := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨htrans (Finset.mem_image_of_mem _ hm), ?_⟩
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hm)
  have hb := endpoint_extension_card_growth T U q hq hTU htranslate
  rw [quotient_region_residue_image S T q hR hsat] at hb
  exact hb

end Erdos345
