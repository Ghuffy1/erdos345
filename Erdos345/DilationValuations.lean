import Erdos345.DilationAnnihilator
import Erdos345.ValuationWindows
import Erdos345.FixedDifferenceValuations

namespace Erdos345

open Finset

def dilationDifference (g k j L : ℕ) : ℕ := g ^ (k * L) - g ^ (j * L)

theorem dilationDifference_pos {g k j L : ℕ}
    (hg : 1 < g) (hj : j < k) (hL : 0 < L) :
    0 < dilationDifference g k j L := by
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hg (Nat.mul_lt_mul_of_pos_right hj hL))

theorem dilationDifference_cast {g k j L : ℕ} (hg : 1 ≤ g) (hj : j ≤ k) :
    (dilationDifference g k j L : ℤ) =
      (g : ℤ) ^ (k * L) - (g : ℤ) ^ (j * L) := by
  rw [dilationDifference, Int.natCast_sub
    (Nat.pow_le_pow_right hg (Nat.mul_le_mul_right L hj))]
  simp only [Int.natCast_pow]

theorem dilationDifference_factor {g k j L : ℕ} (hj : j ≤ k) :
    dilationDifference g k j L = g ^ (j * L) * (g ^ ((k - j) * L) - 1) := by
  rw [dilationDifference, nat_power_difference_factor g (Nat.mul_le_mul_right L hj),
    ← Nat.sub_mul]

/-- A nonzero explicit dilation product gives an exact valuation budget. -/
theorem primePower_le_dilation_valuation_sum
    (S : Finset ℕ) (m L : ℕ → ℕ) (g p e k : ℕ)
    (hp : p.Prime) (hg : 1 < g) (hS : ∀ n ∈ S, 0 < n)
    (hL : ∀ n ∈ S, 0 < L n) (hm : ∀ n ∈ S, m n ≤ k)
    (hperiod : ∀ n ∈ S, Nat.ModEq n (g ^ L n) 1)
    (hpower : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    e ≤ ∑ n ∈ S, ∑ j ∈ range (m n),
      (dilationDifference g k j (L n)).factorization p := by
  have hpos (n : ℕ) (hn : n ∈ S) (j : ℕ) (hj : j ∈ range (m n)) :
      0 < dilationDifference g k j (L n) :=
    dilationDifference_pos hg (lt_of_lt_of_le (mem_range.mp hj) (hm n hn)) (hL n hn)
  have hcast :
      ((∏ n ∈ S, ∏ j ∈ range (m n), dilationDifference g k j (L n) : ℕ) : ℤ) =
        ∏ n ∈ S, ∏ j ∈ range (m n),
          ((g : ℤ) ^ (k * L n) - (g : ℤ) ^ (j * L n)) := by
    push_cast
    apply prod_congr rfl
    intro n hn
    apply prod_congr rfl
    intro j hj
    exact dilationDifference_cast hg.le (le_trans (mem_range.mp hj).le (hm n hn))
  have hd : p ^ e ∣ ∏ n ∈ S, ∏ j ∈ range (m n), dilationDifference g k j (L n) := by
    apply Int.natCast_dvd_natCast.mp
    rw [hcast]
    exact power_annihilator_dilation_product_dvd S m L g (p ^ e) k hS hperiod hpower
  have hnonzero : (∏ n ∈ S, ∏ j ∈ range (m n), dilationDifference g k j (L n)) ≠ 0 := by
    apply ne_of_gt
    apply prod_pos
    intro n hn
    exact prod_pos (hpos n hn)
  have hb := (hp.pow_dvd_iff_le_factorization hnonzero).mp hd
  rw [Nat.factorization_prod_apply (fun n hn =>
    (ne_of_gt (prod_pos (hpos n hn))))] at hb
  calc
    e ≤ ∑ n ∈ S, (∏ j ∈ range (m n), dilationDifference g k j (L n)).factorization p := hb
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      exact Nat.factorization_prod_apply (fun j hj => ne_of_gt (hpos n hn j hj))

theorem dilationDifference_five_factorization {k j L : ℕ}
    (hj : j < k) (hL : 0 < L) :
    (dilationDifference 5 k j L).factorization 2 =
      2 + (k - j).factorization 2 + L.factorization 2 := by
  have hdiff : k - j ≠ 0 := by omega
  have hmain : emultiplicity 2 (dilationDifference 5 k j L) =
      2 + emultiplicity 2 (k - j) + emultiplicity 2 L := by
    rw [dilationDifference_factor hj.le, Nat.prime_two.emultiplicity_mul,
      Nat.prime_two.emultiplicity_pow, emultiplicity_eq_zero.mpr (by decide : ¬2 ∣ (5 : ℕ)),
      mul_zero, zero_add, five_power_sub_one_multiplicity,
      Nat.prime_two.emultiplicity_mul, add_assoc]
  rw [← factorization_cast_eq_emultiplicity Nat.prime_two
      (Nat.ne_of_gt (dilationDifference_pos (by decide) hj hL)),
    ← factorization_cast_eq_emultiplicity Nat.prime_two hdiff,
    ← factorization_cast_eq_emultiplicity Nat.prime_two (Nat.ne_of_gt hL)] at hmain
  exact_mod_cast hmain

end Erdos345
