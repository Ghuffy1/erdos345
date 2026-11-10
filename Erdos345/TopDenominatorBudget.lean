import Erdos345.ProductPigeonhole

namespace Erdos345

open Finset

noncomputable def topDenominator (S : Finset ℕ) (m : ℕ → ℕ) (t : ℕ) : ℝ :=
  (((m t - 1).factorial : ℝ) ^ t.totient) * regularizedCyclotomicNorm S m t

theorem topDenominator_pos
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (t : ℕ) (ht : 0 < t) :
    0 < topDenominator S m t := by
  have hf : (0 : ℝ) < (m t - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  exact mul_pos (pow_pos hf _) (lt_of_lt_of_le zero_lt_one (regularizedCyclotomicNorm_ge_one S m hS t ht))

/-- The factorial conversion costs at most one further copy of the same
mass/order logarithmic budget. -/
theorem scaled_log_topDenominator_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    (p ^ (k + 1) : ℕ) * Real.log (topDenominator (Icc 1 N) m (p ^ (k + 1))) ≤
      4 * ((p ^ (k + 1)).totient : ℝ) * (weightMass N w : ℝ) * Real.log N := by
  let t := p ^ (k + 1)
  let b := m t - 1
  have ht0 : 0 < t := pow_pos hp.pos _
  have hslot := rootSlots_mul_le_mass hw t
  have hslots : rootSlots N w t ≤ weightMass N w := by nlinarith
  have hbN : b ≤ N := (Nat.sub_le _ _).trans ((hm t ht).trans (hslots.trans hMass))
  have hbt : t * b ≤ weightMass N w :=
    (Nat.mul_le_mul_left t ((Nat.sub_le _ _).trans (hm t ht))).trans hslot
  have hf : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hfbound : (b.factorial : ℝ) ≤ (N : ℝ) ^ b := by
    exact_mod_cast (Nat.factorial_le_pow b).trans (Nat.pow_le_pow_left hbN b)
  have hlogf := Real.log_le_log hf hfbound
  rw [Real.log_pow] at hlogf
  have hbtR : (t : ℝ) * b ≤ weightMass N w := by exact_mod_cast hbt
  have hlogN := Real.log_natCast_nonneg N
  have hfscaled : (t : ℝ) * Real.log (b.factorial : ℝ) ≤ (weightMass N w : ℝ) * Real.log N := by
    have h1 := mul_le_mul_of_nonneg_left hlogf (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    have h2 := mul_le_mul_of_nonneg_right hbtR hlogN
    nlinarith
  have hR := scaled_log_regularizedNorm_le_three hw m hm p k hp ht
  have hphi := mul_le_mul_of_nonneg_left hfscaled (Nat.cast_nonneg t.totient : (0 : ℝ) ≤ t.totient)
  have hS : ∀ n ∈ Icc 1 N, 0 < n := fun n hn => (mem_Icc.mp hn).1
  have hRpos : 0 < regularizedCyclotomicNorm (Icc 1 N) m t :=
    lt_of_lt_of_le zero_lt_one (regularizedCyclotomicNorm_ge_one _ _ hS t ht0)
  change (t : ℝ) * Real.log ((b.factorial : ℝ) ^ t.totient * regularizedCyclotomicNorm (Icc 1 N) m t) ≤ _
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hf)) (ne_of_gt hRpos), Real.log_pow]
  change (t : ℝ) * Real.log (regularizedCyclotomicNorm (Icc 1 N) m t) ≤ _ at hR
  nlinarith [hR, hphi]

theorem log_topDenominator_le
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N)) (hMass : weightMass N w ≤ N)
    (m : ℕ → ℕ) (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) :
    Real.log (topDenominator (Icc 1 N) m (p ^ (k + 1))) ≤
      ((p ^ (k + 1)).totient : ℝ) *
        (4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N) := by
  have ht0 : (0 : ℝ) < (p ^ (k + 1) : ℕ) := by exact_mod_cast pow_pos hp.pos (k + 1)
  have h := scaled_log_topDenominator_le hw hMass m hm p k hp ht
  calc
    _ ≤ (4 * ((p ^ (k + 1)).totient : ℝ) * (weightMass N w : ℝ) * Real.log N) /
        (p ^ (k + 1) : ℕ) := (le_div_iff₀ ht0).mpr (by nlinarith [h])
    _ = _ := by ring

end Erdos345
