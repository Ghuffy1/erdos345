import Erdos345.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace Erdos345

/-- Representation by a finite set of positive bases. -/
def represented (k m : ℕ) : Prop :=
  ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ ∑ b ∈ B, b ^ k = m

theorem represented_iff_mem_subsetSums {k m : ℕ} (hk : 0 < k) :
    represented k m ↔ m ∈ subsetSums (kthPowers k) := by
  classical
  constructor
  · rintro ⟨B, hpos, hsum⟩
    refine ⟨B.image (fun b => b ^ k), ?_, ?_⟩
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨b, hpos b hb, rfl⟩
    · rw [Finset.sum_image]
      · exact hsum.symm
      · intro a _ b _ hab
        exact Nat.pow_left_injective (Nat.ne_of_gt hk) hab
  · rintro ⟨B, hB, hsum⟩
    let root : ℕ → ℕ := fun x =>
      if hx : x ∈ B then Classical.choose (hB hx) else 0
    have hroot : ∀ x (hx : x ∈ B), 0 < root x ∧ (root x) ^ k = x := by
      intro x hx
      dsimp [root]
      rw [dite_eq_left hx]
      exact Classical.choose_spec (hB hx)
    have hinj : ∀ x ∈ B, ∀ y ∈ B, root x = root y → x = y := by
      intro x hx y hy hxy
      calc
        x = (root x) ^ k := (hroot x hx).2.symm
        _ = (root y) ^ k := congrArg (fun a => a ^ k) hxy
        _ = y := (hroot y hy).2
    refine ⟨B.image root, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      exact (hroot x hx).1
    · rw [Finset.sum_image hinj]
      calc
        ∑ x ∈ B, (root x) ^ k = ∑ x ∈ B, x :=
          Finset.sum_congr rfl (fun x hx => (hroot x hx).2)
        _ = m := hsum.symm

theorem represented_zero (k : ℕ) : represented k 0 := by
  exact ⟨∅, by simp, by simp⟩

/-- A represented integer below the next power can only use smaller bases. -/
theorem representation_bases_le {k H m : ℕ}
    (hm : m < (H + 1) ^ k) {B : Finset ℕ}
    (hsum : ∑ b ∈ B, b ^ k = m) :
    ∀ b ∈ B, b ≤ H := by
  intro b hb
  have hle : b ^ k ≤ m := by
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (i ^ k)) hb
  by_contra h
  have hHb : H + 1 ≤ b := by omega
  have hp : (H + 1) ^ k ≤ b ^ k := Nat.pow_le_pow_left hHb k
  omega

/-- Any integer not represented lies strictly below every valid threshold. -/
theorem exception_lt_threshold {k m t : ℕ} (hk : 0 < k)
    (hm : ¬ represented k m) (ht : t ∈ thresholds (kthPowers k)) : m < t := by
  by_contra h
  have htm : t ≤ m := Nat.le_of_not_gt h
  exact hm ((represented_iff_mem_subsetSums hk).mpr (ht m htm))

end Erdos345
