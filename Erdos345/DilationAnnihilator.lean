import Erdos345.DilationAction

namespace Erdos345

open Finset Polynomial

noncomputable def dilationBoundPolynomial (S : Finset ℕ) (m L : ℕ → ℕ) (g : ℕ) : ℤ[X] :=
  ∏ n ∈ S, ∏ j ∈ range (m n), (X ^ L n - C ((g : ℤ) ^ (j * L n)))

theorem cyclotomicProduct_monic (S : Finset ℕ) (m : ℕ → ℕ) :
    (cyclotomicProduct S m).Monic := by
  apply monic_prod_of_monic
  intro n _
  exact (cyclotomic.monic n ℤ).pow (m n)

theorem dilationBoundPolynomial_eval (S : Finset ℕ) (m L : ℕ → ℕ) (g k : ℕ) :
    (dilationBoundPolynomial S m L g).eval ((g : ℤ) ^ k) =
      ∏ n ∈ S, ∏ j ∈ range (m n), ((g : ℤ) ^ (k * L n) - (g : ℤ) ^ (j * L n)) := by
  simp only [dilationBoundPolynomial, eval_prod, eval_sub, eval_pow, eval_X, eval_C, ← pow_mul]

theorem dilationBoundPolynomial_factor (S : Finset ℕ) (m L : ℕ → ℕ) (g n j : ℕ)
    (hn : n ∈ S) (hj : j < m n) :
    (X ^ L n - C ((g : ℤ) ^ (j * L n))) ∣ dilationBoundPolynomial S m L g := by
  have hinner : (X ^ L n - C ((g : ℤ) ^ (j * L n))) ∣
      ∏ t ∈ range (m n), (X ^ L n - C ((g : ℤ) ^ (t * L n))) :=
    dvd_prod_of_mem _ (mem_range.mpr hj)
  exact hinner.trans (dvd_prod_of_mem _ hn)

/-- Component periods give an explicit integral polynomial annihilating
dilation on every solution of the cyclotomic recurrence. -/
theorem dilationBoundPolynomial_annihilates_complex
    (S : Finset ℕ) (m L : ℕ → ℕ) (g : ℕ)
    (hS : ∀ n ∈ S, 0 < n)
    (hperiod : ∀ n ∈ S, Nat.ModEq n (g ^ L n) 1)
    (f : ℕ → ℂ)
    (hf : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℂ)) f = 0) :
    dilationAction g ((dilationBoundPolynomial S m L g).map (Int.castRingHom ℂ)) f = 0 := by
  let z := @cyclotomicRootValue S
  let d := cyclotomicRootMultiplicity (S := S) m
  let ell : CyclotomicRootIndex S → ℕ := fun i => L i.1
  refine split_dilation_annihilator z d ell (cyclotomicRootValue_injective S)
    (cyclotomicRootValue_ne_zero S hS) g
    ((dilationBoundPolynomial S m L g).map (Int.castRingHom ℂ)) ?_ ?_ f ?_
  · intro i
    have hroot := isPrimitiveRoot_of_mem_primitiveRoots i.2.property
    have hpow := pow_eq_pow_of_modEq (hperiod i.1 i.1.property) hroot.pow_eq_one
    simpa only [z, ell, cyclotomicRootValue, pow_one] using hpow
  · intro i j
    have hdiv := Polynomial.map_dvd (Int.castRingHom ℂ)
      (dilationBoundPolynomial_factor S m L g i.1 j i.1.property j.is_lt)
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, map_X,
      Int.coe_castRingHom, Int.cast_pow, Int.cast_natCast] using hdiv
  · rwa [cyclotomicProduct_split S m hS]

theorem dilationBoundPolynomial_annihilates_integer
    (S : Finset ℕ) (m L : ℕ → ℕ) (g : ℕ)
    (hS : ∀ n ∈ S, 0 < n)
    (hperiod : ∀ n ∈ S, Nat.ModEq n (g ^ L n) 1)
    (f : ℕ → ℤ) (hf : shiftAction (cyclotomicProduct S m) f = 0) :
    dilationAction g (dilationBoundPolynomial S m L g) f = 0 := by
  let φ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hfC : shiftAction ((cyclotomicProduct S m).map φ) (fun j => φ (f j)) = 0 := by
    funext n
    rw [shiftAction_map, congrFun hf n]
    simp
  have hC := dilationBoundPolynomial_annihilates_complex S m L g hS hperiod
    (fun j => φ (f j)) hfC
  funext n
  apply Int.cast_injective (α := ℂ)
  have hn := congrFun hC n
  rw [dilationAction_map] at hn
  simpa only [φ, Int.coe_castRingHom, Pi.zero_apply, Int.cast_zero] using hn

/-- This gives the local-scaling divisibility directly from an annihilating
polynomial, without an explicit characteristic-polynomial factorization. -/
theorem power_annihilator_dilation_product_dvd
    (S : Finset ℕ) (m L : ℕ → ℕ) (g q k : ℕ)
    (hS : ∀ n ∈ S, 0 < n)
    (hperiod : ∀ n ∈ S, Nat.ModEq n (g ^ L n) 1)
    (hpower : ∀ n, (q : ℤ) ∣ shiftAction (cyclotomicProduct S m)
      (fun j : ℕ => (j : ℤ) ^ k) n) :
    (q : ℤ) ∣ ∏ n ∈ S, ∏ j ∈ range (m n),
      ((g : ℤ) ^ (k * L n) - (g : ℤ) ^ (j * L n)) := by
  let p := cyclotomicProduct S m
  have hunit : p.leadingCoeff ^ 2 = 1 := by
    rw [(cyclotomicProduct_monic S m).leadingCoeff]
    norm_num
  let f := generatedRecurrence p (fun i => (i : ℤ) ^ k)
  have hf : shiftAction p f = 0 := generatedRecurrence_solution p hunit _
  have hcong : ∀ n, (q : ℤ) ∣ f n - (n : ℤ) ^ k :=
    generated_power_congruence p hunit q k hpower
  have hH := dilationBoundPolynomial_annihilates_integer S m L g hS hperiod f hf
  have hd := dilation_annihilator_divides_value g q k (dilationBoundPolynomial S m L g) f hcong hH
  rwa [dilationBoundPolynomial_eval] at hd

end Erdos345
