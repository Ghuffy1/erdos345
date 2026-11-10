import Erdos345.ResidueEndpointGrowth
import Erdos345.IndexedSumset

namespace Erdos345

open scoped Pointwise

/-- Every residue occupied by S contributes a new point outside A,
provided S contains A and the translate A+q. -/
theorem endpoint_extension_card_growth (A S : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (hA : A ⊆ S) (htranslate : A.image (fun a => a + q) ⊆ S) :
    A.card + (naturalResidueImage S q).card ≤ S.card := by
  classical
  let R := naturalResidueImage S q
  have hex : ∀ r : R, ∃ n : ℕ, n ∈ S ∧ n ∉ A ∧ (n : ZMod q) = r.val := by
    intro r
    by_cases hr : r.val ∈ naturalResidueImage A q
    · obtain ⟨n, hn, hnot, hcast⟩ := exists_new_residue_endpoint A q hq r.val hr
      exact ⟨n, htranslate hn, hnot, hcast⟩
    · obtain ⟨n, hn, hcast⟩ := Finset.mem_image.mp r.prop
      refine ⟨n, hn, ?_, hcast⟩
      intro hnA
      exact hr (Finset.mem_image.mpr ⟨n, hnA, hcast⟩)
  choose f hf using hex
  let D := S \ A
  have hmem (r : R) : f r ∈ D := Finset.mem_sdiff.mpr ⟨(hf r).1, (hf r).2.1⟩
  let g : R → D := fun r => ⟨f r, hmem r⟩
  have hg : Function.Injective g := by
    intro r s hrs
    apply Subtype.ext
    have hfs : f r = f s := congrArg Subtype.val hrs
    exact (hf r).2.2.symm.trans ((congrArg (fun n : ℕ => (n : ZMod q)) hfs).trans (hf s).2.2)
  have hc : R.card ≤ D.card := Finset.card_le_card_of_injective hg
  have hd : D.card + A.card = S.card := Finset.card_sdiff_add_card_eq_card hA
  change A.card + R.card ≤ S.card
  omega

/-- For B containing both 0 and q, growth of the integer sumset is at
least the number of residue classes occupied by the whole new sumset. -/
theorem sumset_residue_growth (A B : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (hzero : 0 ∈ B) (hqB : q ∈ B) :
    A.card + (naturalResidueImage (A + B) q).card ≤ (A + B).card := by
  apply endpoint_extension_card_growth A (A + B) q hq
  · intro a ha
    exact Finset.mem_add.mpr ⟨a, ha, 0, hzero, by omega⟩
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_add.mpr ⟨a, ha, q, hqB, rfl⟩

end Erdos345
