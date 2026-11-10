import Erdos345.DyadicSineSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Erdos345

theorem tsum_ge_initial_sum_of_nonnegative_tail (f : ℕ → ℝ) (hf : Summable f)
    (r : ℕ) (htail : ∀ j, r ≤ j → 0 ≤ f j) :
    (∑ j ∈ Finset.range r, f j) ≤ ∑' j, f j := by
  have heq := hf.sum_add_tsum_nat_add r
  have hpos : 0 ≤ ∑' j, f (j + r) := tsum_nonneg (fun j => htail _ (by omega))
  linarith

theorem dyadicSineTotal_pos_small (P : ℕ → Finset ℕ) (v : ℕ → ℕ) (q : ℕ)
    (hP : ∀ j, P j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2))
    (hv : ∀ j, v j ≤ j + 1) (hP0 : (P 0).Nonempty) (hv0 : v 0 = 1)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < Real.sin (Real.pi * x) + ∑' j, dyadicSineLevel P v j x := by
  have hpos : ∀ j, 0 ≤ dyadicSineLevel P v j x := by
    intro j
    apply dyadicSineLevel_nonneg_tail P v 0 j x hx.le (by omega) (by norm_num; linarith)
    intro p hp
    exact (Finset.mem_Icc.mp (hP j hp)).1
  obtain ⟨p, hp⟩ := hP0
  have hp0 : 0 < p := (Finset.mem_Icc.mp (hP 0 hp)).1
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hblock := scaledSineBlock_small_lower p 1 hp0 (by omega) hx (by simpa using hx1)
  have hblockpos : 0 < scaledSineBlock p 1 x := by
    have hc : 0 < 2 / Real.pi * (1 : ℝ) ^ 2 * p * x := by positivity
    exact hc.trans_le (by simpa only [Nat.cast_one] using hblock)
  have hfirst : 0 < dyadicSineLevel P v 0 x := by
    have hs : scaledSineBlock p 1 x ≤ dyadicSineLevel P v 0 x := by
      change scaledSineBlock p 1 x ≤ ∑ a ∈ P 0, scaledSineBlock a (v 0) (x / 2 ^ 0)
      simp only [pow_zero, div_one, hv0]
      apply Finset.single_le_sum _ hp
      intro a ha
      apply scaledSineBlock_nonneg a 1 ((Finset.mem_Icc.mp (hP 0 ha)).1) hx.le
      have haR : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp (hP 0 ha)).1
      linarith
    exact hblockpos.trans_le hs
  have hsum : dyadicSineLevel P v 0 x ≤ ∑' j, dyadicSineLevel P v j x := by
    have hs := (summable_dyadicSineLevels P v q x hP hv).sum_le_tsum
      ({0} : Finset ℕ) (fun j _ => hpos j)
    simpa using hs
  have hsin : 0 ≤ Real.sin (Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  linarith

end Erdos345
