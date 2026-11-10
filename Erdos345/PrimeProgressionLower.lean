import Erdos345.ShiftedPrimeDoubleCounting
import OAI.NumberTheory.PrimeGaps.MangoldtBounds

namespace Erdos345

open OAI.LargePrimeGaps

theorem prime_mod_one_iff_shift_divides (p d : ℕ) (hp : p.Prime) (hd : 2 ≤ d) :
    p % d = 1 ↔ d ∣ p - 1 := by
  have h1 : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    apply (Nat.modEq_iff_dvd' hp.one_lt.le).mp
    change 1 % d = p % d
    rw [h1, h]
  · intro h
    have hm := (Nat.modEq_iff_dvd' hp.one_lt.le).mpr h
    change 1 % d = p % d at hm
    rw [h1] at hm
    exact hm.symm

theorem prime_progression_theta_eq (X d : ℕ) (hd : 2 ≤ d) :
    residuePrefix theta X d 1 = ∑ p ∈ primesOneMod X d, Real.log p := by
  classical
  change (∑ p ∈ (Finset.Ioc 0 X).filter (fun p => p % d = 1),
    if p.Prime then Real.log p else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, primesOneMod, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_, hpX⟩, hmod⟩, hp⟩
      exact ⟨⟨hpX, hp⟩, (prime_mod_one_iff_shift_divides p d hp hd).mp hmod⟩
    · rintro ⟨⟨hpX, hp⟩, hdiv⟩
      exact ⟨⟨⟨hp.pos, hpX⟩, (prime_mod_one_iff_shift_divides p d hp hd).mpr hdiv⟩, hp⟩
  · intro p _
    rfl

theorem prime_progression_theta_le_card (X d : ℕ) (hd : 2 ≤ d) :
    residuePrefix theta X d 1 ≤ (primesOneMod X d).card * Real.log X := by
  rw [prime_progression_theta_eq X d hd]
  calc
    (∑ p ∈ primesOneMod X d, Real.log p) ≤ ∑ _p ∈ primesOneMod X d, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hm.2.pos) (by exact_mod_cast hm.1)
    _ = _ := by simp

/-- A finite consequence of explicit endpoint and prime-power errors. -/
theorem prime_progression_card_lower (X d : ℕ) (hX : 2 ≤ X) (hd : 2 ≤ d)
    (herror : (endpointError X d : ℝ) ≤ (X : ℝ) / (4 * d.totient))
    (hpower : 2 * Real.sqrt X * Real.log X ≤ (X : ℝ) / (4 * d.totient)) :
    (X : ℝ) / (2 * d.totient * Real.log X) ≤ (primesOneMod X d).card := by
  have hphi : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < d by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have he := endpointClassError_le X (q := d) (c := 1) (by omega) (by simp)
  have hp := residueSlice_primepower_error (U := X) (by omega) 0 d 1
  change |residuePrefix ArithmeticFunction.vonMangoldt X d 1 - residuePrefix theta X d 1|
    ≤ 2 * Real.sqrt X * Real.log X at hp
  have heLower := (abs_sub_le_iff.mp (he.trans herror)).2
  have hpLower := (abs_sub_le_iff.mp (hp.trans hpower)).1
  have ht := prime_progression_theta_le_card X d hd
  have hbound : (X : ℝ) / (2 * d.totient) ≤
      (primesOneMod X d).card * Real.log X := by
    have hid : (X : ℝ) / d.totient - X / (4 * d.totient) - X / (4 * d.totient) =
        X / (2 * d.totient) := by ring
    linarith only [heLower, hpLower, ht, hid]
  rw [← div_div]
  exact (div_le_iff₀ hlog).mpr hbound

end Erdos345
