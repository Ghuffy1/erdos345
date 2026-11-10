import Erdos345.AnalyticInputAssembly
import Erdos345.ShiftedPrimeAsymptotics

namespace Erdos345

/-- Statement of the specialized Belov--Konyagin input used by this
development. This definition is not a proof of that input. -/
def BelovKonyaginInput : Prop :=
  ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
    AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
    (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
      (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
    a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5

/-- Unconditional clause of Fan--Pollack Theorem 1, with the positive
coefficient 0.6736 written exactly as 421/625. This is an unproved input
definition; the source theorem has not yet been formalized here. -/
def FanPollackInput : Prop :=
  ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧
    Real.exp (((421 / 625 : ℝ) * Real.log 2) * Real.log (t : ℝ) /
      Real.log (Real.log (t : ℝ))) < ((shiftedPrimes t).card : ℝ)

/-- All remaining arithmetic, combinatorial, analytic comparison and
logical steps are proved from the two explicitly unproved source inputs.
This theorem must not be presented as an unconditional proof. -/
theorem intended_of_published_analytic_inputs
    (hcosine : BelovKonyaginInput) (hfan : FanPollackInput) : IntendedStatement := by
  apply intended_of_cosine_and_shifted_prime_abundance hcosine
  apply shifted_prime_abundance_of_fan_input ((421 / 625 : ℝ) * Real.log 2)
  · exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  · exact hfan

end Erdos345
