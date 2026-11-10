import Erdos345.FourierPrefixBudget

namespace Erdos345

open Filter

structure FourierParameterConditions (C : ℝ) (k : ℕ) (w : ℕ → ℕ) : Prop where
  degree_large : 20 ≤ k
  coarse_window : 128000 * (k : ℝ) * (fourierH k + 1) ≤ fourierW k
  center_inside : quasipolynomialCenterPrefix k C ≤ unreservedEndpoint (fourierN k) k + 1
  sampling_length : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * fourierW k
  inverse_size : ((fourierW k : ℝ) + 1) *
    (coefficientL1 (flatPolynomial (k + 1) w) ^ 2 * fourierH k / 4 + 1) +
    (flatPolynomial (k + 1) w).natDegree ≤ unreservedEndpoint (fourierN k) k + 1
  perturbation : 2 * fourierH k + 2 * Real.pi ^ 2 * (quasipolynomialCenterPrefix k C : ℝ) *
    (flatInverseRadius k (fourierW k) (fourierH k)) ^ 2 *
    ((quasipolynomialCenterPrefix k C : ℝ) ^ k) ^ 2 ≤ (k : ℝ) ^ 2
  root_budget : Real.log ((fourierN k : ℝ) + 1) ≤ (k : ℝ) * Real.log (3 / 2)

/-- All numerical conditions hold simultaneously for the actual natural
ceilings, uniformly over every flat product with the stated norm. -/
theorem eventually_fourier_parameter_conditions (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ w : ℕ → ℕ,
      weightMass (k + 1) w = k + 1 →
      coefficientL1 (flatPolynomial (k + 1) w) ≤ Real.exp (C * logScale k ^ 6) →
      FourierParameterConditions C k w := by
  filter_upwards [eventually_ge_atTop 20, eventually_fourier_coarse_window,
    eventually_fourier_center_prefix C hC, eventually_fourier_chebyshev_length,
    eventually_fourier_inverse_size C hC, eventually_fourier_energy_margin,
    eventually_fourier_center_separation C hC, eventually_fourier_root_budget]
    with k hk hcoarse hinside hlength hsize henergy hsep hroot
  intro w hmass hnorm
  refine ⟨hk, hcoarse, hinside, hlength, hsize w hmass hnorm, ?_, hroot⟩
  apply perturbation_budget_of_separation k (quasipolynomialCenterPrefix k C)
    (fourierW k) (by omega) (quasipolynomialCenterPrefix_pos k C) (fourierW_pos k)
    (fourierH k) ((k : ℝ) ^ 2)
  · exact coarseWindowRadius_budget k (fourierW k) hk (fourierH k) (fourierH_nonneg k) hcoarse
  · exact hsep
  · exact henergy

end Erdos345
