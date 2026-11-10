import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Erdos345

theorem summable_nat_pow_div_two (d : ℕ) :
    Summable (fun j : ℕ => (j : ℝ) ^ d / 2 ^ j) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
    (r := (1 / 2 : ℝ)) (by norm_num)
  simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using h

theorem summable_succ_pow_div_two (d : ℕ) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ d / 2 ^ j) := by
  have hinj : Function.Injective (fun j : ℕ => j + 1) := by
    intro i j hij
    dsimp only at hij
    omega
  have h := (summable_nat_pow_div_two d).comp_injective hinj
  have hm := h.mul_left 2
  apply hm.congr
  intro j
  dsimp only [Function.comp_apply]
  rw [pow_succ]
  field_simp

end Erdos345
