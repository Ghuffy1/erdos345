import Erdos345.GcdOneGroupSelection
import Erdos345.GroupRepresentation
import Erdos345.LevParameterBounds

namespace Erdos345

/-- All finite input conditions for the remaining interval theorem are
now available together, including integer rounding and distinct-base
representation. The interval theorem itself is not assumed or proved here. -/
theorem good_degrees_interval_ready_groups
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k l n : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧ 3 ≤ n ∧
      2 * levMultiplicityCeil l n < 128 ∧
      (fourierN k + 1) ^ k ≤ 128 * (n - 1) ∧
      l = 2 * (reserveGroupSize (fourierN k) k * fourierN k ^ k) ∧
      ∃ A : Fin 128 → Finset ℕ,
        (∀ j, A j ⊆ Finset.Icc 0 l) ∧
        (∀ j, n ≤ (A j).card) ∧
        (∀ (j : Fin 128) (d a : ℕ), (∀ v ∈ A j, v % d = a % d) → d = 1) ∧
        (∀ f : Fin 128 → ℕ, (∀ j, f j ∈ A j) →
          representedUpTo k (fourierN k) (∑ j, f j)) := by
  classical
  obtain ⟨K, hK⟩ := good_degrees_gcd_one_groups hinput
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hk20, hlarge, J, hsub, hdisj, hcard, hspan, hprogression⟩ := hK Y hY
  let N := fourierN k
  let s := reserveGroupSize N k
  let m := s * N ^ k
  have hN : 128 ≤ N := by dsimp only [N]; omega
  have hs : 4 ≤ s := by
    change 4 ≤ N / (512 * k)
    apply (Nat.le_div_iff_mul_le (show 0 < 512 * k by omega)).mpr
    dsimp only [N]
    omega
  have hp : N ≤ N ^ k := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (show 1 ≤ N by omega) (show 1 ≤ k by omega))
  have hm : 128 ≤ m := by
    have hmul := Nat.mul_le_mul_right (N ^ k) (show 1 ≤ s by omega)
    dsimp only [m]
    omega
  obtain ⟨hn, hceil, hmult⟩ := lev_parameters_large m hm
  refine ⟨k, 2 * m, m / 16, hkY, hk2Y, hk20, hn, hmult, ?_, rfl,
    (fun j => finitePowerSums (J j) k), ?_, ?_, hprogression, ?_⟩
  · exact lev_interval_covers_next_power N k s (by omega) hN (by dsimp only [N]; omega) hs
  · intro j
    apply finitePowerSums_subset_interval
    have hR : ((∑ b ∈ J j, b ^ k : ℕ) : ℝ) < ((2 * m : ℕ) : ℝ) := by
      simpa only [m, s, N, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
        Nat.cast_pow, mul_assoc] using hspan j
    exact_mod_cast hR.le
  · intro j
    have hM : (m : ℝ) / 16 ≤ (finitePowerSums (J j) k).card := by
      simpa only [m, s, N, Nat.cast_mul, Nat.cast_pow] using hcard j
    have hfloor : ((m / 16 : ℕ) : ℝ) ≤ (m : ℝ) / 16 := Nat.cast_div_le
    exact_mod_cast hfloor.trans hM
  · intro f hf
    exact representedUpTo_of_group_sums J k (fourierN k) hsub hdisj f hf

end Erdos345
