import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

namespace Erdos345

noncomputable def naturalResidueImage (A : Finset ℕ) (q : ℕ) : Finset (ZMod q) :=
  A.image (fun n : ℕ => (n : ZMod q))

/-- In each occupied residue class, translating its largest member by q
produces a new point outside the original finite set. -/
theorem exists_new_residue_endpoint (A : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (r : ZMod q) (hr : r ∈ naturalResidueImage A q) :
    ∃ n : ℕ, n ∈ A.image (fun a => a + q) ∧ n ∉ A ∧ (n : ZMod q) = r := by
  classical
  obtain ⟨a₀, ha₀, hr₀⟩ := Finset.mem_image.mp hr
  let S := A.filter (fun a : ℕ => (a : ZMod q) = r)
  have hS : S.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨ha₀, hr₀⟩⟩
  let a := S.max' hS
  have haS : a ∈ S := Finset.max'_mem S hS
  have haA : a ∈ A := (Finset.mem_filter.mp haS).1
  have har : (a : ZMod q) = r := (Finset.mem_filter.mp haS).2
  have hnew : ((a + q : ℕ) : ZMod q) = r := by
    simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using har
  refine ⟨a + q, Finset.mem_image.mpr ⟨a, haA, rfl⟩, ?_, hnew⟩
  intro hn
  have hle := Finset.le_max' S (a + q) (Finset.mem_filter.mpr ⟨hn, hnew⟩)
  change a + q ≤ a at hle
  omega

theorem residue_endpoint_card_growth (A : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    A.card + (naturalResidueImage A q).card ≤
      (A ∪ A.image (fun a => a + q)).card := by
  classical
  let R := naturalResidueImage A q
  choose f hf using (fun r : R => exists_new_residue_endpoint A q hq r.val r.prop)
  let D := (A.image (fun a => a + q)) \ A
  have hmap : ∀ r : R, f r ∈ D := by
    intro r
    exact Finset.mem_sdiff.mpr ⟨(hf r).1, (hf r).2.1⟩
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    exact (hf r).2.2.symm.trans ((congrArg (fun n : ℕ => (n : ZMod q)) hrs).trans (hf s).2.2)
  let g : R → D := fun r => ⟨f r, hmap r⟩
  have hg : Function.Injective g := by
    intro r s hrs
    exact hinj (congrArg Subtype.val hrs)
  have hc : R.card ≤ D.card := Finset.card_le_card_of_injective hg
  have heq : (A ∪ A.image (fun a => a + q)).card = A.card + D.card := by
    rw [← Finset.union_sdiff_self_eq_union]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro n hn hm
    exact (Finset.mem_sdiff.mp hm).2 hn
  rw [heq]
  exact Nat.add_le_add_left hc _

end Erdos345
