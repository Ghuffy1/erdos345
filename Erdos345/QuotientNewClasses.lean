import Erdos345.StabilizerQuotientCard

namespace Erdos345

open scoped Classical Pointwise

/-- Unless a sumset fills the whole finite group, a generating summand
introduces a new class modulo the stabilizer of the full sumset. -/
theorem quotient_new_class_of_generating {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P B : Finset G) (hP : P.Nonempty) (hzero : 0 ∈ B)
    (hgen : AddSubgroup.closure (B : Set G) = ⊤)
    (hne : P + B ≠ Finset.univ) :
    let R := P + B
    let H := AddAction.stabilizer G (R : Set G)
    P.image (QuotientAddGroup.mk : G → G ⧸ H) ⊂
      R.image (QuotientAddGroup.mk : G → G ⧸ H) := by
  classical
  let R := P + B
  let H := AddAction.stabilizer G (R : Set G)
  let π := (QuotientAddGroup.mk' H)
  have hR : R.Nonempty := hP.add ⟨0, hzero⟩
  have hPR : P ⊆ R := by
    intro p hp
    exact Finset.mem_add.mpr ⟨p, hp, 0, hzero, add_zero p⟩
  have hsat : P + R.addStab ⊆ R := by
    calc
      P + R.addStab ⊆ R + R.addStab := Finset.add_subset_add hPR (Finset.Subset.refl _)
      _ = R := Finset.add_addStab R
  change P.image π ⊂ R.image π
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.image_subset_image hPR, ?_⟩
  intro heq
  have hRP : R = P + R.addStab := by
    apply Finset.Subset.antisymm
    · intro g hg
      apply (stabilizer_quotient_mem_image R P hR g).mp
      change π g ∈ P.image π
      rw [heq]
      exact Finset.mem_image_of_mem π hg
    · exact hsat
  have hfixed : R + B = R := by
    calc
      R + B = (P + R.addStab) + B := by rw [← hRP]
      _ = (P + B) + R.addStab := by ac_rfl
      _ = R := Finset.add_addStab R
  have hB : B ⊆ R.addStab := (Finset.add_subset_left_iff hR).mp hfixed.subset
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (AddSubgroup.closure_le H).2
    intro g hg
    change g ∈ (AddAction.stabilizer G (R : Set G) : Set G)
    rw [← Finset.coe_addStab hR]
    exact hB hg
  apply hne
  change R = Finset.univ
  apply Finset.eq_univ_of_forall
  intro g
  have hRcopy := hR
  obtain ⟨r, hr⟩ := hRcopy
  have hd : g - r ∈ R.addStab := by
    change g - r ∈ (R.addStab : Set G)
    rw [Finset.coe_addStab hR]
    change g - r ∈ H
    rw [hH]
    trivial
  rw [← Finset.add_addStab R]
  exact Finset.mem_add.mpr ⟨r, hr, g - r, hd, by abel⟩

end Erdos345
