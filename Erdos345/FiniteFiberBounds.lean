import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos345

theorem fiber_card_defect_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (b : β) (d : ℕ)
    (hb : b ∈ S.image f) (hf : ∀ c ∈ S.image f, (S.filter (fun a => f a = c)).card ≤ d) :
    S.card + d ≤ (S.filter (fun a => f a = b)).card + (S.image f).card * d := by
  classical
  let R := S.image f
  have hsum : S.card = (S.filter (fun a => f a = b)).card +
      ∑ c ∈ R.erase b, (S.filter (fun a => f a = c)).card := by
    rw [Finset.card_eq_sum_card_image f S]
    exact (Finset.add_sum_erase R (fun c => (S.filter (fun a => f a = c)).card) hb).symm
  have hrest : (∑ c ∈ R.erase b, (S.filter (fun a => f a = c)).card) ≤ (R.erase b).card * d := by
    calc
      _ ≤ ∑ _c ∈ R.erase b, d := Finset.sum_le_sum (fun c hc => hf c (Finset.mem_of_mem_erase hc))
      _ = _ := by simp
  calc
    S.card + d ≤ (S.filter (fun a => f a = b)).card + ((R.erase b).card * d + d) := by omega
    _ = (S.filter (fun a => f a = b)).card + ((R.erase b).card + 1) * d := by ring
    _ = _ := by rw [Finset.card_erase_add_one hb]

theorem image_filter_preimage {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : β → γ) (c : γ) :
    (S.filter (fun a => g (f a) = c)).image f = (S.image f).filter (fun b => g b = c) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hga⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hga⟩
  · rintro ⟨⟨a, ha, rfl⟩, hga⟩
    exact ⟨a, ⟨ha, hga⟩, rfl⟩

theorem fiber_card_le_preimage_card {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : β → γ) (c : γ) :
    ((S.image f).filter (fun b => g b = c)).card ≤ (S.filter (fun a => g (f a) = c)).card := by
  rw [← image_filter_preimage]
  exact Finset.card_image_le

end Erdos345
