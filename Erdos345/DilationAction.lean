import Erdos345.CyclotomicExpansion

namespace Erdos345

open Finset Polynomial

noncomputable def sequenceDilation (R : Type*) [CommRing R] (g : ℕ) :
    Module.End R (ℕ → R) where
  toFun f n := f (g * n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def dilationAction {R : Type*} [CommRing R] (g : ℕ) (H : R[X]) :
    Module.End R (ℕ → R) := aeval (sequenceDilation R g) H

theorem sequenceDilation_pow {R : Type*} [CommRing R]
    (g h : ℕ) (f : ℕ → R) (n : ℕ) :
    (sequenceDilation R g ^ h) f n = f (g ^ h * n) := by
  induction h generalizing n with
  | zero => simp [sequenceDilation]
  | succ h ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (sequenceDilation R g ^ h) f (g * n) = f (g ^ (h + 1) * n)
    rw [ih, pow_succ]
    congr 1
    ring

theorem dilationAction_sum {R : Type*} [CommRing R]
    (g : ℕ) (H : R[X]) (f : ℕ → R) (n : ℕ) :
    dilationAction g H f n =
      ∑ j ∈ range (H.natDegree + 1), H.coeff j * f (g ^ j * n) := by
  rw [dilationAction, aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, sequenceDilation_pow]

theorem dilationAction_mul {R : Type*} [CommRing R]
    (g : ℕ) (P Q : R[X]) (f : ℕ → R) :
    dilationAction g (P * Q) f = dilationAction g P (dilationAction g Q f) := by
  simp only [dilationAction, map_mul, Module.End.mul_apply]

theorem dilationAction_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : ℕ) (H : R[X]) (f : ℕ → R) (n : ℕ) :
    dilationAction g (H.map φ) (fun j => φ (f j)) n = φ (dilationAction g H f n) := by
  rw [dilationAction, aeval_eq_sum_range'
    (natDegree_map_le.trans_lt (Nat.lt_succ_self H.natDegree))]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, sequenceDilation_pow, coeff_map]
  rw [dilationAction_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_mul]

theorem dilationAction_factor_exponential {K : Type*} [Field K]
    (g j L : ℕ) (z : K) (hperiod : z ^ (g ^ L) = z) :
    dilationAction g (X ^ L - C ((g : K) ^ (j * L))) (exponentialPower z j) = 0 := by
  have hiter : (sequenceDilation K g ^ L) (exponentialPower z j) =
      (g : K) ^ (j * L) • exponentialPower z j := by
    funext n
    rw [sequenceDilation_pow]
    have hexp := congrFun (exponentialPower_dilate z j (g ^ L)) n
    rw [hperiod] at hexp
    simpa only [Nat.cast_pow, Pi.smul_apply, smul_eq_mul, ← pow_mul, Nat.mul_comm L j] using hexp
  simp only [dilationAction, map_sub, aeval_X_pow, aeval_C,
    Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [hiter, sub_self]

theorem dilationAction_multiple_kills_exponential {K : Type*} [Field K]
    (g j L : ℕ) (z : K) (hperiod : z ^ (g ^ L) = z) (H : K[X])
    (hdiv : (X ^ L - C ((g : K) ^ (j * L))) ∣ H) :
    dilationAction g H (exponentialPower z j) = 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, mul_comm, dilationAction_mul, dilationAction_factor_exponential g j L z hperiod, map_zero]

/-- Component periods suffice to annihilate dilation on every solution; an
explicit characteristic-polynomial determinant is unnecessary for this step. -/
theorem split_dilation_annihilator {K I : Type*} [Field K] [CharZero K] [Fintype I]
    (z : I → K) (m L : I → ℕ) (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0)
    (g : ℕ) (H : K[X]) (hperiod : ∀ i, z i ^ (g ^ L i) = z i)
    (hdiv : ∀ i (j : Fin (m i)), (X ^ L i - C ((g : K) ^ ((j : ℕ) * L i))) ∣ H)
    (f : ℕ → K) (hf : shiftAction (linearFactorProduct z m) f = 0) :
    dilationAction g H f = 0 := by
  obtain ⟨c, hc⟩ := split_recurrence_expansion z m hinj hz f hf
  rw [hc, map_sum]
  apply sum_eq_zero
  intro ij _
  rw [map_smul, dilationAction_multiple_kills_exponential g ij.2 (L ij.1) (z ij.1)
    (hperiod ij.1) H (hdiv ij.1 ij.2), smul_zero]

theorem dilationAction_power_at_one (g k : ℕ) (H : ℤ[X]) :
    dilationAction g H (fun n : ℕ => (n : ℤ) ^ k) 1 = H.eval ((g : ℤ) ^ k) := by
  rw [dilationAction_sum, eval_eq_sum_range]
  apply sum_congr rfl
  intro j _
  simp only [Nat.mul_one, Nat.cast_pow, ← pow_mul, Nat.mul_comm j k]

theorem dilationAction_congruence (g q : ℕ) (H : ℤ[X]) (f h : ℕ → ℤ)
    (hcong : ∀ n, (q : ℤ) ∣ f n - h n) (n : ℕ) :
    (q : ℤ) ∣ dilationAction g H f n - dilationAction g H h n := by
  rw [dilationAction_sum, dilationAction_sum, ← sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right (hcong _) _

theorem dilation_annihilator_divides_value (g q k : ℕ) (H : ℤ[X]) (f : ℕ → ℤ)
    (hcong : ∀ n, (q : ℤ) ∣ f n - (n : ℤ) ^ k) (hH : dilationAction g H f = 0) :
    (q : ℤ) ∣ H.eval ((g : ℤ) ^ k) := by
  have h := dilationAction_congruence g q H f (fun n : ℕ => (n : ℤ) ^ k) hcong 1
  rw [congrFun hH 1, dilationAction_power_at_one] at h
  simpa only [Pi.zero_apply, zero_sub, dvd_neg] using h

end Erdos345
