import Erdos345.FiniteFiberBounds

namespace Erdos345

theorem image_filter_mem {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (P : Finset β) :
    (S.filter (fun a => f a ∈ P)).image f = S.image f ∩ P := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hp⟩
  · rintro ⟨⟨a, ha, rfl⟩, hp⟩
    exact ⟨a, ⟨ha, hp⟩, rfl⟩

theorem image_filter_mem_preimage {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : β → γ) (P : Finset γ) :
    (S.filter (fun a => g (f a) ∈ P)).image f =
      (S.image f).filter (fun b => g b ∈ P) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hp⟩
  · rintro ⟨⟨a, ha, rfl⟩, hp⟩
    exact ⟨a, ⟨ha, hp⟩, rfl⟩

theorem fiber_partition_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (P : Finset β) :
    (S.filter (fun a => f a ∈ P)).card +
        (S.filter (fun a => f a ∈ S.image f \ P)).card = S.card := by
  have heq : S.filter (fun a => f a ∈ S.image f \ P) =
      S.filter (fun a => f a ∉ P) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, Finset.mem_image_of_mem f h.1, h.2⟩
  rw [heq]
  exact Finset.card_filter_add_card_filter_not ..

theorem fiber_region_card_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (P : Finset β) :
    (S.filter (fun a => f a ∈ P)).card =
      ∑ b ∈ P, (S.filter (fun a => f a = b)).card := by
  exact (Finset.sum_card_fiberwise_eq_card_filter S P f).symm

end Erdos345
