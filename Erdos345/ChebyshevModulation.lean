import Erdos345.MixedGramEnergy

namespace Erdos345

open Finset Complex
open scoped ComplexConjugate

theorem unitGrid_mem (L n : ℕ) (hL : 0 < L) (hn : n ≤ L) :
    (n : ℝ) / L ∈ Set.Icc (0 : ℝ) 1 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  exact ⟨div_nonneg (Nat.cast_nonneg _) hLR.le,
    (div_le_one hLR).mpr (by exact_mod_cast hn)⟩

theorem unitGrid_step_abs (L n : ℕ) (hL : 0 < L) :
    |((n + 1 : ℕ) : ℝ) / L - (n : ℝ) / L| = 1 / (L : ℝ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have heq : ((n + 1 : ℕ) : ℝ) / L - (n : ℝ) / L = 1 / (L : ℝ) := by push_cast; ring
  rw [heq, abs_of_pos (by positivity)]

noncomputable def chebyshevPhase {D : ℕ} (z : ℂ) (c : Fin D → ℂ) (L n : ℕ) : ℂ :=
  modulatedSequence z (fun n => shiftedChebyshevSeries c ((n : ℝ) / L)) n

theorem chebyshevPhase_norm {D : ℕ} (z : ℂ) (hz : ‖z‖ = 1)
    (c : Fin D → ℂ) (L n : ℕ) :
    ‖chebyshevPhase z c L n‖ = ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ := by
  simp only [chebyshevPhase, modulatedSequence, norm_mul, norm_pow, hz, one_pow, mul_one]

theorem chebyshev_sample_step_le {D : ℕ} (c : Fin D → ℂ) (B : ℝ)
    (hB : chebyshevCoefficientMass c ≤ B) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n < L - 1) :
    ‖shiftedChebyshevSeries c (((n + 1 : ℕ) : ℝ) / L) -
      shiftedChebyshevSeries c ((n : ℝ) / L)‖ ≤ (2 * (D : ℝ) ^ 2 * B) / L := by
  have h := shiftedChebyshevSeries_difference_le c
    (unitGrid_mem L (n + 1) hL (by omega)) (unitGrid_mem L n hL (by omega))
  rw [unitGrid_step_abs L n hL] at h
  have hmul := mul_le_mul_of_nonneg_left hB
    (by positivity : 0 ≤ 2 * (D : ℝ) ^ 2 * (1 / L))
  ring_nf at h hmul ⊢
  nlinarith

theorem chebyshevPhase_cross_bound {D : ℕ} (a b : Fin D → ℂ)
    (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (B δ : ℝ) (hB : 0 ≤ B) (ha : chebyshevCoefficientMass a ≤ B)
    (hb : chebyshevCoefficientMass b ≤ B) (hδ : 0 < δ) (hsep : δ ≤ ‖conj x * y - 1‖)
    (L : ℕ) (hL : 0 < L) :
    ‖∑ n ∈ range L, conj (chebyshevPhase x a L n) * chebyshevPhase y b L n‖ ≤
      (1 + 4 * (D : ℝ) ^ 2) * B ^ 2 * (2 / δ) := by
  have h := modulated_discreteGram_offDiagonal_le
    (fun n => shiftedChebyshevSeries a ((n : ℝ) / L))
    (fun n => shiftedChebyshevSeries b ((n : ℝ) / L)) x y hx hy L hL B
    (2 * (D : ℝ) ^ 2 * B) δ hB (by positivity) hδ hsep
    (fun n hn => (shiftedChebyshevSeries_norm_le a (unitGrid_mem L n hL hn.le)).trans ha)
    (fun n hn => (shiftedChebyshevSeries_norm_le b (unitGrid_mem L n hL hn.le)).trans hb)
    (fun n hn => chebyshev_sample_step_le a B ha L hL n hn)
    (fun n hn => chebyshev_sample_step_le b B hb L hL n hn)
  change ‖∑ n ∈ range L, conj (chebyshevPhase x a L n) * chebyshevPhase y b L n‖ ≤ _ at h
  convert h using 1
  ring

theorem chebyshev_sample_energy_mass_lower {D : ℕ} (hD : 0 < D)
    (c : Fin D → ℂ) (L : ℕ) (hL : 0 < L) :
    (L : ℝ) * (Real.pi / (32 * (D : ℝ))) * (∑ j, ‖c j‖ ^ 2) -
      4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2 ≤
        ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have he := (abs_le.mp (shiftedChebyshevSeries_sampling_error c L hL)).1
  have hl := shiftedChebyshevSeries_continuous_energy_lower hD c
  have hn : (Real.pi / (32 * (D : ℝ))) * (∑ j, ‖c j‖ ^ 2) -
      (4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2) / L ≤
        (1 / (L : ℝ)) * ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hn hLR.le
  calc
    _ = (L : ℝ) * ((Real.pi / (32 * (D : ℝ))) * (∑ j, ‖c j‖ ^ 2) -
        (4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2) / L) := by field_simp
    _ ≤ (L : ℝ) * ((1 / (L : ℝ)) * ∑ n ∈ range L,
        ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2) := hmul
    _ = _ := by field_simp

end Erdos345
