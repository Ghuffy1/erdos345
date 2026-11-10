import Erdos345.RoundingEnergy

namespace Erdos345

noncomputable def finiteSineEnergy (R : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ R, Real.sin (Real.pi * f n) ^ 2

noncomputable def finiteCosineMean (R : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ R, Real.cos (Real.pi * f n) ^ 2) / R.card

theorem finiteSineEnergy_nonneg (R : Finset ℕ) (f : ℕ → ℝ) :
    0 ≤ finiteSineEnergy R f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteSineEnergy_le_card (R : Finset ℕ) (f : ℕ → ℝ) :
    finiteSineEnergy R f ≤ R.card := by
  calc
    _ ≤ ∑ _n ∈ R, (1 : ℝ) := Finset.sum_le_sum (fun n _ => by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * f n),
        sq_nonneg (Real.cos (Real.pi * f n))])
    _ = _ := by simp

theorem finiteCosineMean_nonneg (R : Finset ℕ) (f : ℕ → ℝ) :
    0 ≤ finiteCosineMean R f :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem finiteCosineMean_eq_one_sub (R : Finset ℕ) (hR : R.Nonempty) (f : ℕ → ℝ) :
    finiteCosineMean R f = 1 - finiteSineEnergy R f / R.card := by
  have hM : (R.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hR).ne'
  have hsum : finiteSineEnergy R f +
      (∑ n ∈ R, Real.cos (Real.pi * f n) ^ 2) = R.card := by
    rw [finiteSineEnergy, ← Finset.sum_add_distrib]
    simp only [Real.sin_sq_add_cos_sq, Finset.sum_const, nsmul_eq_mul, mul_one]
  dsimp only [finiteCosineMean]
  field_simp
  linarith

theorem finiteCosineMean_le_one (R : Finset ℕ) (hR : R.Nonempty) (f : ℕ → ℝ) :
    finiteCosineMean R f ≤ 1 := by
  rw [finiteCosineMean_eq_one_sub R hR f]
  have h := div_nonneg (finiteSineEnergy_nonneg R f) (Nat.cast_nonneg (α := ℝ) R.card)
  linarith

/-- The exact sine/cosine identity gives the exponential bound for every
finite population, without a probabilistic independence assumption. -/
theorem finiteCosineMean_pow_le (R : Finset ℕ) (hR : R.Nonempty) (f : ℕ → ℝ) (t : ℕ) :
    finiteCosineMean R f ^ t ≤
      Real.exp (-(t : ℝ) * finiteSineEnergy R f / R.card) := by
  have h : finiteCosineMean R f ≤ Real.exp (-(finiteSineEnergy R f / R.card)) := by
    rw [finiteCosineMean_eq_one_sub R hR f]
    exact Real.one_sub_le_exp_neg _
  calc
    _ ≤ Real.exp (-(finiteSineEnergy R f / R.card)) ^ t :=
      pow_le_pow_left₀ (finiteCosineMean_nonneg R f) h t
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem finiteCosineMean_pow_le_of_energy (R : Finset ℕ) (hR : R.Nonempty)
    (f : ℕ → ℝ) (t : ℕ) (H : ℝ) (hH : H ≤ finiteSineEnergy R f) :
    finiteCosineMean R f ^ t ≤ Real.exp (-(t : ℝ) * H / R.card) := by
  refine (finiteCosineMean_pow_le R hR f t).trans (Real.exp_le_exp.mpr ?_)
  have hM : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonpos_left hH (neg_nonpos.mpr (Nat.cast_nonneg _))) hM

theorem sum_cosineMean_pow_le_of_energy (R S : Finset ℕ) (hR : R.Nonempty)
    (f : ℕ → ℕ → ℝ) (t : ℕ) (H : ℝ)
    (hH : ∀ h ∈ S, H ≤ finiteSineEnergy R (f h)) :
    (∑ h ∈ S, finiteCosineMean R (f h) ^ t) ≤
      S.card * Real.exp (-(t : ℝ) * H / R.card) := by
  calc
    _ ≤ ∑ _h ∈ S, Real.exp (-(t : ℝ) * H / R.card) :=
      Finset.sum_le_sum (fun h hh => finiteCosineMean_pow_le_of_energy R hR (f h) t H (hH h hh))
    _ = _ := by simp

end Erdos345
