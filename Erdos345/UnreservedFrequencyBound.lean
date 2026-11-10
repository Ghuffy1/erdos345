import Erdos345.CoarseWindowBudget
import Erdos345.CollisionLogBudget

namespace Erdos345

/-- Coarse but explicit window conditions imply an empty exceptional
grid and a uniform collision bound for the actual unreserved sampling
population. The original center and recurrence-size conditions remain
visible; no unproved small-numerator estimate is an input. -/
theorem coarse_unreserved_frequency_bound (N c k F W X : ℕ) (w : ℕ → ℕ)
    (hc : 0 < c) (hcN : c ≤ N) (hk : 20 ≤ k)
    (hw : AntitoneOn w (Set.Iio F)) (hmass : weightMass F w = k + 1)
    (H E : ℝ) (hH : 0 ≤ H) (hWN : W ≤ N)
    (hW : 128000 * (k : ℝ) * (H + 1) ≤ W)
    (hXV : X ≤ unreservedEndpoint N k + 1)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial F w) ^ 2 * H / 4 + 1) +
      (flatPolynomial F w).natDegree ≤ unreservedEndpoint N k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k u b X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E)
    (hroot : Real.log ((N : ℝ) + 1) ≤ (k : ℝ) * Real.log (3 / 2)) :
    (nonzeroFrequencies (c ^ k) ∩ lowEnergyGrid (c ^ k) k (unreservedEndpoint N k + 1) H = ∅) ∧
    ∀ t : ℕ, powerCollisionSum (unreservedPopulation N k) k (c ^ k) t ≤
      ((c ^ k : ℕ) : ℝ) *
        Real.exp (-(t : ℝ) * (H - 257) / (unreservedPopulation N k).card) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hbase : 128000 * (k : ℝ) ≤ W := by nlinarith [mul_nonneg hk0 hH]
  have hW4 : 4 ≤ W := by
    have h : (4 : ℝ) ≤ W := by linarith
    exact_mod_cast h
  have hW0 : 0 < W := by omega
  have hWN' : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hNk : 32 * (k : ℝ) ≤ N := by linarith
  have hNA : (4128 : ℝ) ≤ N := by linarith
  have hscale := coarseWindowScale_conditions k W hk H hH hW
  have hradius := coarseWindowRadius_budget k W hk H hH hW
  have hempty := unreserved_lowEnergyGrid_empty N c k F W X w hc hcN hk hw hmass H E
    ((W : ℝ) / 8) hXV hW0 hlarge hsize hcenter hbudget
    (flatInverseRadius_le_one k W hW4 H hradius) hscale.1
    (flatInverseRadius_eighth_scale k W hW0 H hradius) (by linarith [hscale.2.2])
    hscale.2.1 hNk hNA hroot (coarseWindowFloor_gt N k W hk H hH hWN hW)
  exact ⟨hempty, fun t => unreserved_collisionSum_le N (c ^ k) k t hk hNk H hempty⟩

theorem unreserved_collision_le_exp_margin (N q k t : ℕ) (hk : 20 ≤ k)
    (hNk : 32 * (k : ℝ) ≤ N) (H s : ℝ)
    (hempty : nonzeroFrequencies q ∩ lowEnergyGrid q k (unreservedEndpoint N k + 1) H = ∅)
    (hmargin : Real.log (q : ℝ) - (t : ℝ) * (H - 257) / (unreservedPopulation N k).card ≤ -s) :
    powerCollisionSum (unreservedPopulation N k) k q t ≤ Real.exp (-s) := by
  have h := unreserved_collisionSum_le N q k t hk hNk H hempty
  apply h.trans
  apply nat_mul_exp_le_exp
  simpa only [sub_eq_add_neg, neg_mul, neg_div] using hmargin

end Erdos345
