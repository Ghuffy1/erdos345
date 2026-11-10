import Erdos345.FiniteResidueDistribution

namespace Erdos345

theorem addChar_sum_product {ι A : Type*} [AddCommMonoid A]
    (ψ : AddChar A ℂ) (S : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ S, f i) = ∏ i ∈ S, ψ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

noncomputable def bitSum {ι : Type*} [Fintype ι] {q : ℕ} (a : ι → ZMod q)
    (ω : ι → Bool) : ZMod q := ∑ i, if ω i then a i else 0

theorem character_bitSum {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (a : ι → ZMod q) (h : ZMod q) (ω : ι → Bool) :
    ZMod.stdAddChar (h * bitSum a ω) =
      ∏ i, if ω i then ZMod.stdAddChar (h * a i) else 1 := by
  unfold bitSum
  rw [Finset.mul_sum, addChar_sum_product]
  apply Finset.prod_congr rfl
  intro i _
  cases ω i <;> simp

theorem bitSum_fourier_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} [NeZero q] (a : ι → ZMod q) (h : ZMod q) :
    cyclicFourier (fun r => (residueMass (bitSum a) r : ℂ)) h =
      ∏ i, (1 + ZMod.stdAddChar (h * a i)) / 2 := by
  rw [residueMass_fourier]
  have heq : (fun ω : ι → Bool => ZMod.stdAddChar (h * bitSum a ω)) =
      (fun ω : ι → Bool => ∏ i, if ω i then ZMod.stdAddChar (h * a i) else 1) := by
    funext ω
    exact character_bitSum a h ω
  rw [heq, uniformMean_pi_prod (fun (i : ι) (b : Bool) =>
    if b then ZMod.stdAddChar (h * a i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp [uniformMean]
  ring

theorem half_character_norm (θ : ℝ) :
    ‖(1 + Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)) / 2‖ ^ 2 = Real.cos θ ^ 2 := by
  rw [norm_div, div_pow]
  rw [show ‖(2 : ℂ)‖ ^ 2 = (4 : ℝ) by norm_num]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
    Complex.add_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_add]
  have hs := Real.sin_sq_add_cos_sq (2 * θ)
  have hc := Real.cos_two_mul θ
  nlinarith

theorem half_stdAddChar_norm (q h a : ℕ) [NeZero q] :
    ‖(1 + ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q))) / 2‖ ^ 2 =
      Real.cos (Real.pi * ((h : ℝ) / q * a)) ^ 2 := by
  have heq : ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q)) =
      Complex.exp (((2 * (Real.pi * ((h : ℝ) / q * a)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Nat.cast_mul]
    have hcast : ((h * a : ℕ) : ZMod q) = ((h * a : ℕ) : ℤ) := by simp
    rw [hcast, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [heq]
  exact half_character_norm _

end Erdos345
