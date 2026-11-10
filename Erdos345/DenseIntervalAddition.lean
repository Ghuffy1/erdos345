import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos345

/-- A direct pigeonhole version of the dense two-sum interval lemma.
No additive-combinatorial structure theorem is an assumption. -/
theorem dense_int_sumset_interval (A B : Finset ℤ) (L₁ L₂ : ℕ)
    (hA : A ⊆ Finset.Icc 0 (L₁ : ℤ)) (hB : B ⊆ Finset.Icc 0 (L₂ : ℤ))
    (hL₁ : (L₁ : ℤ) ≤ (A.card + B.card : ℕ) - 2)
    (hL₂ : (L₂ : ℤ) ≤ (A.card + B.card : ℕ) - 2)
    (g : ℤ) (hlo : (L₁ : ℤ) + L₂ - ((A.card + B.card : ℕ) - 2) ≤ g)
    (hhi : g ≤ (A.card + B.card : ℕ) - 2) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = g := by
  classical
  let R := B.image (fun b => g - b)
  let U := Finset.Icc (min 0 (g - L₂)) (max (L₁ : ℤ) g)
  have hAU : A ⊆ U := by
    intro a ha
    have ha' := Finset.mem_Icc.mp (hA ha)
    apply Finset.mem_Icc.mpr
    omega
  have hRU : R ⊆ U := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    have hb' := Finset.mem_Icc.mp (hB hb)
    apply Finset.mem_Icc.mpr
    omega
  have hRcard : R.card = B.card := by
    change (B.image (fun b => g - b)).card = B.card
    apply Finset.card_image_of_injective
    intro a b hab
    change g - a = g - b at hab
    omega
  have hUcard : (U.card : ℤ) = max (L₁ : ℤ) g + 1 - min 0 (g - L₂) := by
    change ((Finset.Icc (min 0 (g - L₂)) (max (L₁ : ℤ) g)).card : ℤ) = _
    rw [Int.card_Icc]
    omega
  have hU : U.card < A.card + R.card := by
    rw [hRcard]
    have h : (U.card : ℤ) < (A.card + B.card : ℕ) := by omega
    exact_mod_cast h
  obtain ⟨a, ha⟩ := Finset.inter_nonempty_of_card_lt_card_add_card hAU hRU hU
  obtain ⟨haA, haR⟩ := Finset.mem_inter.mp ha
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haR
  exact ⟨a, haA, b, hb, by omega⟩

/-- Natural-number form with an inclusive interval of endpoint
difference twice the density excess. -/
theorem dense_nat_sumset_interval (A B : Finset ℕ) (L₁ L₂ : ℕ)
    (hA : A ⊆ Finset.Icc 0 L₁) (hB : B ⊆ Finset.Icc 0 L₂)
    (hL₁ : L₁ + 2 ≤ A.card + B.card) (hL₂ : L₂ + 2 ≤ A.card + B.card)
    (g : ℕ) (hlo : L₁ + L₂ ≤ g + (A.card + B.card - 2))
    (hhi : g ≤ A.card + B.card - 2) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = g := by
  classical
  let A' := A.image (fun a : ℕ => (a : ℤ))
  let B' := B.image (fun b : ℕ => (b : ℤ))
  have hcast : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n hmn
    change (m : ℤ) = (n : ℤ) at hmn
    exact Int.ofNat.inj hmn
  have hAi : A'.card = A.card := Finset.card_image_of_injective _ hcast
  have hBi : B'.card = B.card := Finset.card_image_of_injective _ hcast
  have hAs : A' ⊆ Finset.Icc 0 (L₁ : ℤ) := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    have hn' := Finset.mem_Icc.mp (hA hn)
    exact Finset.mem_Icc.mpr ⟨by positivity, by exact_mod_cast hn'.2⟩
  have hBs : B' ⊆ Finset.Icc 0 (L₂ : ℤ) := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    have hn' := Finset.mem_Icc.mp (hB hn)
    exact Finset.mem_Icc.mpr ⟨by positivity, by exact_mod_cast hn'.2⟩
  have h₁ : (L₁ : ℤ) ≤ (A'.card + B'.card : ℕ) - 2 := by
    rw [hAi, hBi]
    omega
  have h₂ : (L₂ : ℤ) ≤ (A'.card + B'.card : ℕ) - 2 := by
    rw [hAi, hBi]
    omega
  have hg₁ : (L₁ : ℤ) + L₂ - ((A'.card + B'.card : ℕ) - 2) ≤ g := by
    rw [hAi, hBi]
    omega
  have hg₂ : (g : ℤ) ≤ (A'.card + B'.card : ℕ) - 2 := by
    rw [hAi, hBi]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := dense_int_sumset_interval A' B' L₁ L₂ hAs hBs h₁ h₂ g hg₁ hg₂
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨u, hu, v, hv, by exact_mod_cast hab⟩

end Erdos345
