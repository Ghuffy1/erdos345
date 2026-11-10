import Erdos345.UniformFourierEnergy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

namespace Erdos345

noncomputable def uniformMean {α 𝕂 : Type*} [Fintype α] [Field 𝕂] [CharZero 𝕂]
    (f : α → 𝕂) : 𝕂 := (∑ a, f a) / (Fintype.card α : 𝕂)

theorem uniformMean_const {α 𝕂 : Type*} [Fintype α] [Nonempty α] [Field 𝕂] [CharZero 𝕂]
    (c : 𝕂) : uniformMean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : 𝕂) ≠ 0 := by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
  simp only [uniformMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem uniformMean_add {α 𝕂 : Type*} [Fintype α] [Field 𝕂] [CharZero 𝕂]
    (f g : α → 𝕂) : uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp only [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sum {α β 𝕂 : Type*} [Fintype α] [Fintype β] [Field 𝕂] [CharZero 𝕂]
    (f : α → β → 𝕂) : uniformMean (fun a => ∑ b, f a b) = ∑ b, uniformMean (fun a => f a b) := by
  simp only [uniformMean, Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformMean_finset_sum {α β 𝕂 : Type*} [Fintype α] [Field 𝕂] [CharZero 𝕂]
    (S : Finset β) (f : α → β → 𝕂) :
    uniformMean (fun a => ∑ b ∈ S, f a b) = ∑ b ∈ S, uniformMean (fun a => f a b) := by
  simp only [uniformMean, Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformMean_mul_const {α 𝕂 : Type*} [Fintype α] [Field 𝕂] [CharZero 𝕂]
    (f : α → 𝕂) (c : 𝕂) : uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp only [uniformMean]
  rw [← Finset.sum_mul]
  ring

theorem uniformMean_nonneg {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ uniformMean f := by
  apply div_nonneg (Finset.sum_nonneg (fun a _ => hf a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ) (hfg : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => hfg a)) (Nat.cast_nonneg _)

/-- Exact factorization of a uniform average over a finite product.
It supplies the independence calculation for the label model. -/
theorem uniformMean_pi_prod {ι κ 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Field 𝕂] [CharZero 𝕂] (f : ι → κ → 𝕂) :
    uniformMean (fun ω : ι → κ => ∏ i, f i (ω i)) = ∏ i, uniformMean (f i) := by
  classical
  simp only [uniformMean, Fintype.card_fun, Nat.cast_pow, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

theorem uniformMean_ite_eq {α 𝕂 : Type*} [Fintype α] [DecidableEq α]
    [Field 𝕂] [CharZero 𝕂] (a₀ : α) (x : 𝕂) :
    uniformMean (fun a : α => if a = a₀ then x else 1) =
      1 - (1 - x) / (Fintype.card α : 𝕂) := by
  have hcN : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a₀⟩
  have hc : (Fintype.card α : 𝕂) ≠ 0 := by exact_mod_cast hcN.ne'
  have hsum : (∑ a : α, if a = a₀ then x else 1) = (Fintype.card α : 𝕂) + (x - 1) := by
    calc
      _ = ∑ a : α, (1 + if a = a₀ then x - 1 else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a = a₀ <;> simp [h]
      _ = _ := by simp [Finset.sum_add_distrib]
  unfold uniformMean
  rw [hsum]
  field_simp
  ring

end Erdos345
