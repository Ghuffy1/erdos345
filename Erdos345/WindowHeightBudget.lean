import Erdos345.ConductorDivisibility

namespace Erdos345

open Finset

noncomputable def energyHeightConstant (N : ℕ) (E : ℝ) : ℝ :=
  max 0 (Real.log E - Real.log (Real.pi / (64 * (N : ℝ))))

noncomputable def windowHeightBudget (N J q L : ℕ) (E : ℝ) : ℝ :=
  max 0 (max
    ((energyHeightConstant N E + 2 * Real.log q + 4 * (J : ℝ) * Real.log N) / Real.log L)
    (((N : ℝ) * energyHeightConstant N E + 8 * (J : ℝ) * Real.log N) / Real.log L))

theorem windowHeightBudget_nonneg (N J q L : ℕ) (E : ℝ) :
    0 ≤ windowHeightBudget N J q L E := le_max_left _ _

theorem weighted_primePower_height_bound (N J L t m : ℕ) (ht : 0 < t) (htN : t ≤ N)
    (hL : (16 : ℝ) ≤ L) (E : ℝ)
    (hm : (m : ℝ) ≤
      (Real.log E + 8 * ((J : ℝ) / t) * Real.log N -
        Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) :
    (t : ℝ) * m ≤
      ((N : ℝ) * energyHeightConstant N E + 8 * (J : ℝ) * Real.log N) / Real.log L := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have htNR : (t : ℝ) ≤ N := by exact_mod_cast htN
  have hC : Real.log E - Real.log (Real.pi / (64 * (N : ℝ))) ≤ energyHeightConstant N E :=
    le_max_right _ _
  have hC0 : 0 ≤ energyHeightConstant N E := le_max_left _ _
  have hprod : (t : ℝ) * (Real.log E - Real.log (Real.pi / (64 * (N : ℝ)))) ≤
      (N : ℝ) * energyHeightConstant N E :=
    (mul_le_mul_of_nonneg_left hC htR.le).trans (mul_le_mul_of_nonneg_right htNR hC0)
  calc
    (t : ℝ) * m ≤ t * ((Real.log E + 8 * ((J : ℝ) / t) * Real.log N -
        Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) :=
      mul_le_mul_of_nonneg_left hm htR.le
    _ = ((t : ℝ) * (Real.log E - Real.log (Real.pi / (64 * (N : ℝ)))) +
        8 * (J : ℝ) * Real.log N) / Real.log L := by
      field_simp [ne_of_gt htR, ne_of_gt hlog]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hlog.le

theorem height_bounds_to_uniform (N J q L : ℕ) (m : ℕ → ℕ)
    (hL : (16 : ℝ) ≤ L) (E : ℝ)
    (hprime : ∀ p a : ℕ, p.Prime → p ^ (a + 1) ∈ Icc 1 N → 0 < m (p ^ (a + 1)) →
      (m (p ^ (a + 1)) : ℝ) ≤
        (Real.log E + 8 * ((J : ℝ) / (p ^ (a + 1) : ℕ)) * Real.log N -
          Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L)
    (hroot : 0 < m 1 → (m 1 : ℝ) ≤
      (Real.log E + 2 * Real.log q + 4 * (J : ℝ) * Real.log N -
        Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L) :
    (m 1 : ℝ) ≤ windowHeightBudget N J q L E ∧
      ∀ p : ℕ, p.Prime → ∀ n ∈ primaryOrders (Icc 1 N) p, n ≠ 1 →
        (n : ℝ) * m n ≤ windowHeightBudget N J q L E := by
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have hC : Real.log E - Real.log (Real.pi / (64 * (N : ℝ))) ≤ energyHeightConstant N E :=
    le_max_right _ _
  constructor
  · by_cases hm : m 1 = 0
    · rw [hm, Nat.cast_zero]
      exact windowHeightBudget_nonneg _ _ _ _ _
    · calc
        (m 1 : ℝ) ≤ _ := hroot (Nat.pos_of_ne_zero hm)
        _ ≤ (energyHeightConstant N E + 2 * Real.log q + 4 * (J : ℝ) * Real.log N) / Real.log L :=
          div_le_div_of_nonneg_right (by linarith) hlog.le
        _ ≤ windowHeightBudget N J q L E := (le_max_left _ _).trans (le_max_right _ _)
  · intro p hp n hn hn1
    by_cases hm : m n = 0
    · rw [hm, Nat.cast_zero, mul_zero]
      exact windowHeightBudget_nonneg _ _ _ _ _
    · obtain ⟨hnS, a, ha⟩ := (mem_primaryOrders (Icc 1 N) p n).mp hn
      cases a with
      | zero => simp only [pow_zero] at ha; exact False.elim (hn1 ha)
      | succ a =>
        rw [ha]
        have ht : p ^ (a + 1) ∈ Icc 1 N := by simpa only [ha] using hnS
        have hmt : 0 < m (p ^ (a + 1)) := by simpa only [ha] using Nat.pos_of_ne_zero hm
        exact (weighted_primePower_height_bound N J L (p ^ (a + 1)) (m (p ^ (a + 1)))
          (pow_pos hp.pos _) (mem_Icc.mp ht).2 hL E (hprime p a hp ht hmt)).trans
          ((le_max_right _ _).trans (le_max_right _ _))

theorem flat_multiplicity_le_power_degree {N : ℕ} {w : ℕ → ℕ}
    (hw : AntitoneOn w (Set.Iio N)) (k : ℕ) (hk : 0 < k)
    (hMass : weightMass N w ≤ k + 1) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n) (hroot : m 1 ≤ k) :
    ∀ n ∈ Icc 1 N, m n ≤ k := by
  intro n hn
  by_cases hn1 : n = 1
  · simpa only [hn1] using hroot
  · have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hslots := rootSlots_mul_le_mass hw n
    have hbound := hm n hn
    nlinarith

end Erdos345
