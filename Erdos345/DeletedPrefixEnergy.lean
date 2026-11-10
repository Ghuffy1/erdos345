import Erdos345.CosineCollision

namespace Erdos345

theorem finiteSineEnergy_range (f : ℕ → ℝ) (V : ℕ) :
    finiteSineEnergy (Finset.range V) f = sineEnergy f V := rfl

theorem finiteSineEnergy_mono (R S : Finset ℕ) (hRS : R ⊆ S) (f : ℕ → ℝ) :
    finiteSineEnergy R f ≤ finiteSineEnergy S f :=
  Finset.sum_le_sum_of_subset_of_nonneg hRS (fun _ _ _ => sq_nonneg _)

/-- Each missing base loses at most one unit of squared-sine energy.
This controls the actual available population, not an idealized prefix. -/
theorem finiteSineEnergy_le_add_missing (R S : Finset ℕ) (f : ℕ → ℝ) :
    finiteSineEnergy S f ≤ finiteSineEnergy R f + (S \ R).card := by
  classical
  let A := S ∩ R
  have hAS : A ⊆ S := Finset.inter_subset_left
  have hAR : A ⊆ R := Finset.inter_subset_right
  have hdiff : S \ A = S \ R := by ext n; simp [A]
  have hsplit : finiteSineEnergy (S \ A) f + finiteSineEnergy A f =
      finiteSineEnergy S f := Finset.sum_sdiff hAS
  rw [hdiff] at hsplit
  have hbound := add_le_add (finiteSineEnergy_le_card (S \ R) f)
    (finiteSineEnergy_mono A R hAR f)
  linarith

theorem prefixEnergy_le_population_add_missing (R : Finset ℕ) (f : ℕ → ℝ) (V : ℕ) :
    sineEnergy f V ≤ finiteSineEnergy R f + ((Finset.range V) \ R).card :=
  finiteSineEnergy_le_add_missing R (Finset.range V) f

theorem populationEnergy_ge_prefix_sub_missing (R : Finset ℕ) (f : ℕ → ℝ)
    (V : ℕ) (D H : ℝ) (hmissing : (((Finset.range V) \ R).card : ℝ) ≤ D)
    (hprefix : H ≤ sineEnergy f V) :
    H - D ≤ finiteSineEnergy R f := by
  have h := prefixEnergy_le_population_add_missing R f V
  linarith

end Erdos345
