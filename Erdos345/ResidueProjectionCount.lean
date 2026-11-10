import Erdos345.ResidueEndpointGrowth
import Mathlib.Tactic

namespace Erdos345

/-- Within [0,q], the only nontrivial collision modulo q is the pair 0,q. -/
theorem natCast_eq_on_closed_interval (q x y : ℕ) (hq : 0 < q)
    (hx : x ≤ q) (hy : y ≤ q) :
    (x : ZMod q) = (y : ZMod q) ↔
      x = y ∨ (x = 0 ∧ y = q) ∨ (x = q ∧ y = 0) := by
  constructor
  · intro h
    have hv : x % q = y % q := by
      simpa only [ZMod.val_natCast] using congrArg (fun z : ZMod q => z.val) h
    by_cases hxq : x = q
    · subst x
      by_cases hyq : y = q
      · exact Or.inl hyq.symm
      · rw [Nat.mod_self, Nat.mod_eq_of_lt (by omega : y < q)] at hv
        exact Or.inr (Or.inr ⟨rfl, hv.symm⟩)
    · by_cases hyq : y = q
      · subst y
        rw [Nat.mod_eq_of_lt (by omega : x < q), Nat.mod_self] at hv
        exact Or.inr (Or.inl ⟨hv, rfl⟩)
      · rw [Nat.mod_eq_of_lt (by omega : x < q), Nat.mod_eq_of_lt (by omega : y < q)] at hv
        exact Or.inl hv
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact congrArg (fun n : ℕ => (n : ZMod q)) h
    · simp
    · simp

theorem naturalResidueImage_card_of_not_both_endpoints (A : Finset ℕ) (q : ℕ)
    (hq : 0 < q) (hA : A ⊆ Finset.Icc 0 q) (hends : ¬ (0 ∈ A ∧ q ∈ A)) :
    (naturalResidueImage A q).card = A.card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have h := (natCast_eq_on_closed_interval q x y hq
    (Finset.mem_Icc.mp (hA hx)).2 (Finset.mem_Icc.mp (hA hy)).2).mp hxy
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact False.elim (hends ⟨hx, hy⟩)
  · exact False.elim (hends ⟨hy, hx⟩)

theorem naturalResidueImage_card_closed_interval (A : Finset ℕ) (q : ℕ)
    (hq : 0 < q) (hA : A ⊆ Finset.Icc 0 q) :
    (naturalResidueImage A q).card = if 0 ∈ A ∧ q ∈ A then A.card - 1 else A.card := by
  classical
  by_cases hends : 0 ∈ A ∧ q ∈ A
  · rw [ite_eq_left hends]
    have himage : naturalResidueImage A q = naturalResidueImage (A.erase q) q := by
      apply Finset.Subset.antisymm
      · intro r hr
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
        by_cases hxq : x = q
        · subst x
          exact Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨by omega, hends.1⟩, by simp⟩
        · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxq, hx⟩, rfl⟩
      · exact Finset.image_subset_image (Finset.erase_subset _ _)
    rw [himage, naturalResidueImage_card_of_not_both_endpoints (A.erase q) q hq
      ((Finset.erase_subset _ _).trans hA) (by simp), Finset.card_erase_of_mem hends.2]
  · rw [ite_eq_right hends]
    exact naturalResidueImage_card_of_not_both_endpoints A q hq hA hends

end Erdos345
