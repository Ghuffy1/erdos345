import Erdos345.PrimeProgressionLower

namespace Erdos345

open Filter OAI.LargePrimeGaps
open scoped Topology

theorem endpointError_le_sum (X Q d : ℕ) (hd : d ∈ Finset.Icc 1 Q) :
    (endpointError X d : ℝ) ≤ ∑ q ∈ Finset.Icc 1 Q, (endpointError X q : ℝ) := by
  exact Finset.single_le_sum (fun q _ => (endpointError X q).coe_nonneg) hd

/-- A bounded-modulus consequence with every numerical prerequisite explicit. -/
theorem prime_progression_uniform_of_bounds (X : ℕ) (b M : ℝ) (hX : 2 ≤ X)
    (hM : 0 < M) (hL : 8 ≤ Real.log (X : ℝ))
    (hcut : (Real.log (X : ℝ)) ^ (24 + b) ≤ (X : ℝ) ^ (1 / 2 : ℝ))
    (hMlog : 4 * M ≤ (Real.log (X : ℝ)) ^ 6)
    (hpower : (Real.log (X : ℝ)) ^ 26 ≤ Real.sqrt (X : ℝ))
    (hsum : (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ) *
      (Real.log (X : ℝ)) ^ (-b)⌋₊, (endpointError X q : ℝ)) ≤
      M * X * (Real.log (X : ℝ)) ^ (-30 : ℝ)) :
    ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ (Real.log (X : ℝ)) ^ 24 →
      (X : ℝ) / (2 * d.totient * Real.log (X : ℝ)) ≤ (primesOneMod X d).card := by
  intro d hd hdL
  let L := Real.log (X : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hphi : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < d by omega)
  have hphiL : (d.totient : ℝ) ≤ L ^ 24 :=
    (show (d.totient : ℝ) ≤ d by exact_mod_cast Nat.totient_le d).trans hdL
  have hcut' : L ^ 24 ≤ (X : ℝ) ^ (1 / 2 : ℝ) * L ^ (-b) := by
    calc
      L ^ 24 = L ^ (24 + b) * L ^ (-b) := by
        rw [← Real.rpow_add hL0]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hcut (by positivity)
  have hdQ : d ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ) * L ^ (-b)⌋₊ := by
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor (hdL.trans hcut')⟩
  have he := (endpointError_le_sum X _ d hdQ).trans hsum
  have hneg : L ^ (-30 : ℝ) = (L ^ 30)⁻¹ := by
    norm_num [Real.rpow_neg hL0.le]
  have heBound : (endpointError X d : ℝ) ≤ (X : ℝ) / (4 * d.totient) := by
    apply he.trans
    rw [hneg]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d.totient)).mpr
    have hm := mul_le_mul_of_nonneg_right hMlog (pow_nonneg hL0.le 24)
    have hph := mul_le_mul_of_nonneg_left hphiL (by positivity : 0 ≤ 4 * M)
    have hmain : 4 * M * (d.totient : ℝ) ≤ L ^ 30 := by
      calc
        4 * M * (d.totient : ℝ) ≤ 4 * M * L ^ 24 := hph
        _ ≤ L ^ 6 * L ^ 24 := hm
        _ = L ^ 30 := by ring
    have hi : 4 * M * (d.totient : ℝ) * (L ^ 30)⁻¹ ≤ 1 :=
      (mul_inv_le_iff₀ (pow_pos hL0 30)).mpr (by simpa using hmain)
    have hx := mul_le_mul_of_nonneg_left hi hX0.le
    nlinarith only [hx]
  have hpBound : 2 * Real.sqrt (X : ℝ) * L ≤ (X : ℝ) / (4 * d.totient) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d.totient)).mpr
    have h8 : 8 * L ^ 25 ≤ L ^ 26 := by
      have hm := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0.le 25)
      calc
        8 * L ^ 25 ≤ L * L ^ 25 := hm
        _ = L ^ 26 := by ring
    have hm : 8 * L * (d.totient : ℝ) ≤ Real.sqrt (X : ℝ) := by
      calc
        8 * L * (d.totient : ℝ) ≤ 8 * L * L ^ 24 :=
          mul_le_mul_of_nonneg_left hphiL (by positivity)
        _ = 8 * L ^ 25 := by ring
        _ ≤ L ^ 26 := h8
        _ ≤ Real.sqrt (X : ℝ) := hpower
    have hx := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (X : ℝ))
    have hs := Real.sq_sqrt hX0.le
    nlinarith only [hx, hs]
  exact prime_progression_card_lower X d hX hd heBound hpBound

end Erdos345
