import Erdos345.IntegerSumsetGrowth
import Erdos345.NaturalResidueGeneration
import Erdos345.ResidueProjectionCount

namespace Erdos345

open scoped Classical Pointwise

/-- Lev's integer growth inequality for sets normalized into [0,q].
The last summand has both endpoints and is in no proper progression. -/
theorem lev_integer_growth {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (j : ι) (hj : j ∈ I)
    (hA : ∀ i ∈ I, (A i).Nonempty) (q : ℕ) (hq : 0 < q) [NeZero q]
    (hbound : ∀ i ∈ I, A i ⊆ Finset.Icc 0 q)
    (hzero : 0 ∈ A j) (hendpoint : q ∈ A j)
    (hprimitive : ∀ d a : ℕ, (∀ n ∈ A j, n % d = a % d) → d = 1) :
    (∑ i ∈ I.erase j, A i).card +
        min q ((∑ i ∈ I, if 0 ∈ A i ∧ q ∈ A i then (A i).card - 1 else (A i).card) +
          1 - I.card) ≤ (∑ i ∈ I, A i).card := by
  have hg := natural_residue_generates_of_no_progression (A j) q hprimitive
  have hb := integer_sumset_growth_of_generating I A j hj hA q hq hzero hendpoint hg
  have heq : (∑ i ∈ I, (naturalResidueImage (A i) q).card) =
      ∑ i ∈ I, if 0 ∈ A i ∧ q ∈ A i then (A i).card - 1 else (A i).card := by
    apply Finset.sum_congr rfl
    intro i hi
    exact naturalResidueImage_card_closed_interval (A i) q hq (hbound i hi)
  rwa [heq] at hb

theorem lev_uniform_growth {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset ℕ) (j : ι) (hj : j ∈ I)
    (q n : ℕ) (hq : 0 < q) [NeZero q] (hn : 2 ≤ n)
    (hcard : ∀ i ∈ I, n ≤ (A i).card)
    (hbound : ∀ i ∈ I, A i ⊆ Finset.Icc 0 q)
    (hzero : 0 ∈ A j) (hendpoint : q ∈ A j)
    (hprimitive : ∀ d a : ℕ, (∀ v ∈ A j, v % d = a % d) → d = 1) :
    (∑ i ∈ I.erase j, A i).card + min q (I.card * (n - 2) + 1) ≤
      (∑ i ∈ I, A i).card := by
  have hA : ∀ i ∈ I, (A i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    have hc := hcard i hi
    omega
  have hb := lev_integer_growth I A j hj hA q hq hbound hzero hendpoint hprimitive
  let f := fun i => if 0 ∈ A i ∧ q ∈ A i then (A i).card - 1 else (A i).card
  have hsum : I.card * (n - 1) ≤ ∑ i ∈ I, f i := by
    calc
      I.card * (n - 1) = ∑ _i ∈ I, (n - 1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hc := hcard i hi
        dsimp only [f]
        split_ifs <;> omega
  have heq : I.card * (n - 1) = I.card * (n - 2) + I.card := by
    have heq' : n - 1 = (n - 2) + 1 := by omega
    rw [heq', Nat.mul_add, mul_one]
  have hm : I.card * (n - 2) + 1 ≤ (∑ i ∈ I, f i) + 1 - I.card := by omega
  have hmin := min_le_min_left q hm
  exact (Nat.add_le_add_left hmin _).trans hb

end Erdos345
