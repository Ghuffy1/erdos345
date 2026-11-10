import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace Erdos345

open Finset

def valuationWindow (p k m : ℕ) : ℕ :=
  ∑ j ∈ range m, (k - j).factorization p

/-- A consecutive valuation sum splits exactly into a factorial term and the
valuation of a binomial coefficient. Every factor is positive when m≤k. -/
theorem valuationWindow_eq (p k m : ℕ) (hm : m ≤ k) :
    valuationWindow p k m = m.factorial.factorization p + (k.choose m).factorization p := by
  have hprod := Nat.factorization_prod_apply (p := p)
    (S := range m) (g := fun j => k - j) (fun j hj => by
      have hjm := mem_range.mp hj
      omega)
  rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose] at hprod
  rw [Nat.factorization_mul (Nat.factorial_ne_zero m) (Nat.choose_ne_zero hm), Finsupp.add_apply] at hprod
  exact hprod.symm

theorem factorial_valuation_scaled_le (p m : ℕ) (hp : p.Prime) :
    (p - 1) * m.factorial.factorization p ≤ m := by
  let : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial]
  exact Nat.sub_le _ _

/-- An exact integer version of the short-window valuation bound. -/
theorem valuationWindow_scaled_le (p k m : ℕ) (hp : p.Prime) (hm : m ≤ k) :
    (p - 1) * valuationWindow p k m ≤ m + (p - 1) * Nat.log p k := by
  rw [valuationWindow_eq p k m hm, Nat.mul_add]
  exact Nat.add_le_add (factorial_valuation_scaled_le p m hp)
    (Nat.mul_le_mul_left _ Nat.factorization_choose_le_log)

theorem valuationWindow_real_le (p k m : ℕ) (hp : p.Prime) (hm : m ≤ k) :
    (valuationWindow p k m : ℝ) ≤
      (m : ℝ) / ((p : ℝ) - 1) + (Nat.log p k : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hbound : ((p : ℝ) - 1) * (valuationWindow p k m : ℝ) ≤
      (m : ℝ) + ((p : ℝ) - 1) * (Nat.log p k : ℝ) := by
    have h := valuationWindow_scaled_le p k m hp hm
    have hpNat : 1 ≤ p := hp.one_lt.le
    exact_mod_cast h
  have hd : 0 < (p : ℝ) - 1 := by linarith
  calc
    (valuationWindow p k m : ℝ) ≤
        ((m : ℝ) + ((p : ℝ) - 1) * (Nat.log p k : ℝ)) / ((p : ℝ) - 1) :=
      (le_div_iff₀ hd).mpr (by nlinarith [hbound])
    _ = (m : ℝ) / ((p : ℝ) - 1) + (Nat.log p k : ℝ) := by field_simp

def multipleWindow (d k m : ℕ) : Finset ℕ :=
  (range m).filter fun j => d ∣ k - j

theorem multipleWindow_card_le (d k m : ℕ) (hm : m ≤ k) :
    (multipleWindow d k m).card ≤ m / d + 1 := by
  classical
  have hmod (j : ℕ) (hj : j ∈ multipleWindow d k m) : j % d = k % d := by
    have hjm := mem_range.mp (mem_filter.mp hj).1
    exact (Nat.modEq_iff_dvd' (by omega : j ≤ k)).mpr (mem_filter.mp hj).2
  have hinj : Set.InjOn (fun j : ℕ => j / d) (↑(multipleWindow d k m) : Set ℕ) := by
    intro i hi j hj hdiv
    have hiMod := hmod i hi
    have hjMod := hmod j hj
    have hiSplit := Nat.div_add_mod i d
    have hjSplit := Nat.div_add_mod j d
    dsimp only at hdiv
    rw [hdiv, hiMod] at hiSplit
    rw [hjMod] at hjSplit
    omega
  have hsub : (multipleWindow d k m).image (fun j => j / d) ⊆ range (m / d + 1) := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    have hjm := mem_range.mp (mem_filter.mp hj).1
    have hdiv : j / d ≤ m / d := Nat.div_le_div_right (show j ≤ m by omega)
    exact mem_range.mpr (by omega)
  calc
    (multipleWindow d k m).card =
        ((multipleWindow d k m).image (fun j => j / d)).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ (range (m / d + 1)).card := card_le_card hsub
    _ = m / d + 1 := card_range _

theorem multipleWindow_card_scaled_le (d k m : ℕ) (hm : m ≤ k) :
    d * (multipleWindow d k m).card ≤ m + d := by
  have hcount := Nat.mul_le_mul_left d (multipleWindow_card_le d k m hm)
  have hfloor := Nat.div_mul_le_self m d
  nlinarith

def rootOneWindow (p k m : ℕ) : ℕ :=
  ∑ j ∈ multipleWindow (p - 1) k m, (1 + (k - j).factorization p)

theorem rootOneWindow_le (p k m : ℕ) :
    rootOneWindow p k m ≤ (multipleWindow (p - 1) k m).card + valuationWindow p k m := by
  rw [rootOneWindow, sum_add_distrib]
  simp only [sum_const, smul_eq_mul, mul_one]
  apply Nat.add_le_add_left
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- The root-one congruence class is bounded without reindexing its valuations:
count its elements, then dominate its valuation sum by the full window. -/
theorem rootOneWindow_scaled_le (p k m : ℕ) (hp : p.Prime) (hm : m ≤ k) :
    (p - 1) * rootOneWindow p k m ≤ 2 * m + (p - 1) * (Nat.log p k + 1) := by
  have hcount := multipleWindow_card_scaled_le (p - 1) k m hm
  have hval := valuationWindow_scaled_le p k m hp hm
  calc
    (p - 1) * rootOneWindow p k m ≤
        (p - 1) * (multipleWindow (p - 1) k m).card + (p - 1) * valuationWindow p k m := by
      simpa only [Nat.mul_add] using Nat.mul_le_mul_left (p - 1) (rootOneWindow_le p k m)
    _ ≤ (m + (p - 1)) + (m + (p - 1) * Nat.log p k) := Nat.add_le_add hcount hval
    _ = _ := by ring

theorem rootOneWindow_real_le (p k m : ℕ) (hp : p.Prime) (hm : m ≤ k) :
    (rootOneWindow p k m : ℝ) ≤
      2 * (m : ℝ) / ((p : ℝ) - 1) + (Nat.log p k : ℝ) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hbound : ((p : ℝ) - 1) * (rootOneWindow p k m : ℝ) ≤
      2 * (m : ℝ) + ((p : ℝ) - 1) * ((Nat.log p k : ℝ) + 1) := by
    have h := rootOneWindow_scaled_le p k m hp hm
    have hpNat : 1 ≤ p := hp.one_lt.le
    exact_mod_cast h
  calc
    (rootOneWindow p k m : ℝ) ≤
        (2 * (m : ℝ) + ((p : ℝ) - 1) * ((Nat.log p k : ℝ) + 1)) / ((p : ℝ) - 1) :=
      (le_div_iff₀ hd).mpr (by nlinarith)
    _ = _ := by field_simp; ring

end Erdos345
