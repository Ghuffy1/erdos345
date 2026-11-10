import Erdos345.SaturatedExpansion

namespace Erdos345

open Finset Polynomial

theorem divisors_eq_filter_Icc {h N : ℕ} (hh : 0 < h) (hN : h ≤ N) :
    h.divisors = (Icc 1 N).filter (fun n => n ∣ h) := by
  ext n
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · intro hn
    exact ⟨⟨Nat.pos_of_dvd_of_pos hn.1 hh, (Nat.le_of_dvd hh hn.1).trans hN⟩, hn.1⟩
  · intro hn
    exact ⟨hn.2, Nat.ne_of_gt hh⟩

theorem X_power_sub_one_power_cyclotomic (N i b : ℕ) (hi : i < N) :
    ((X : ℤ[X]) ^ (i + 1) - 1) ^ b =
      ∏ n ∈ Icc 1 N, (cyclotomic n ℤ) ^ (if n ∣ i + 1 then b else 0) := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < i + 1),
    ← Finset.prod_pow, divisors_eq_filter_Icc (h := i + 1) (N := N) (by omega) (by omega),
    prod_filter]
  apply prod_congr rfl
  intro n _
  split_ifs <;> simp

theorem flatPolynomial_cyclotomic_factorization (N : ℕ) (a : ℕ → ℕ) :
    ((-1 : ℤ[X]) ^ weightMass N a) * flatPolynomial N a =
      cyclotomicProduct (Icc 1 N) (rootSlots N a) := by
  have hswap : (∏ i ∈ range N, ((X : ℤ[X]) ^ (i + 1) - 1) ^ a i) =
      cyclotomicProduct (Icc 1 N) (rootSlots N a) := by
    calc
      _ = ∏ i ∈ range N, ∏ n ∈ Icc 1 N,
          (cyclotomic n ℤ) ^ (if n ∣ i + 1 then a i else 0) := by
        apply prod_congr rfl
        intro i hi
        exact X_power_sub_one_power_cyclotomic N i (a i) (mem_range.mp hi)
      _ = ∏ n ∈ Icc 1 N, ∏ i ∈ range N,
          (cyclotomic n ℤ) ^ (if n ∣ i + 1 then a i else 0) := prod_comm
      _ = _ := by
        apply prod_congr rfl
        intro n _
        rw [prod_pow_eq_pow_sum]
        rfl
  have hsign : flatPolynomial N a =
      (-1 : ℤ[X]) ^ weightMass N a * ∏ i ∈ range N, (X ^ (i + 1) - 1) ^ a i := by
    rw [flatPolynomial]
    calc
      _ = ∏ i ∈ range N, ((-1 : ℤ[X]) * (X ^ (i + 1) - 1)) ^ a i := by
        apply prod_congr rfl
        intro i _
        congr 1
        ring
      _ = _ := by
        simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, weightMass]
  rw [hsign, ← mul_assoc, ← mul_pow]
  norm_num only [neg_mul_neg, one_mul, one_pow]
  exact hswap

theorem flatCyclotomic_annihilates (N : ℕ) (a : ℕ → ℕ) (f : ℕ → ℚ)
    (hf : shiftAction ((flatPolynomial N a).map (Int.castRingHom ℚ)) f = 0) :
    shiftAction ((cyclotomicProduct (Icc 1 N) (rootSlots N a)).map (Int.castRingHom ℚ)) f = 0 := by
  rw [← flatPolynomial_cyclotomic_factorization, Polynomial.map_mul,
    shiftAction_mul, hf, shiftAction_zero_sequence]

/-- The integer flat recurrence gives the actual minimal cyclotomic
annihilator with every multiplicity bounded by the corresponding root slot. -/
theorem exists_minimal_flat_cyclotomic_annihilator (N : ℕ) (a : ℕ → ℕ) (f : ℕ → ℚ)
    (hf : shiftAction ((flatPolynomial N a).map (Int.castRingHom ℚ)) f = 0) :
    ∃ h : ℕ → ℕ, (∀ n ∈ Icc 1 N, h n ≤ rootSlots N a n) ∧
      (cyclotomicProduct (Icc 1 N) h).map (Int.castRingHom ℚ) = minimalAnnihilator f := by
  exact exists_minimal_cyclotomic_annihilator (Icc 1 N) (rootSlots N a)
    (fun n hn => (mem_Icc.mp hn).1) f (flatCyclotomic_annihilates N a f hf)

theorem exists_minimal_flat_slot_bound {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) (f : ℕ → ℚ)
    (hf : shiftAction ((flatPolynomial N a).map (Int.castRingHom ℚ)) f = 0) :
    ∃ h : ℕ → ℕ,
      (∀ n ∈ Icc 1 N, h n ≤ rootSlots N a n ∧ n * h n ≤ weightMass N a) ∧
      (cyclotomicProduct (Icc 1 N) h).map (Int.castRingHom ℚ) = minimalAnnihilator f := by
  obtain ⟨h, hh, heq⟩ := exists_minimal_flat_cyclotomic_annihilator N a f hf
  refine ⟨h, ?_, heq⟩
  intro n hn
  exact ⟨hh n hn, (Nat.mul_le_mul_left n (hh n hn)).trans (rootSlots_mul_le_mass ha n)⟩

end Erdos345
