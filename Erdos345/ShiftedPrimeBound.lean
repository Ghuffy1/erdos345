import Erdos345.FixedDifferenceValuations

namespace Erdos345

def shiftedPrimes (h : ℕ) : Finset ℕ :=
  (Finset.range (h + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ h)

def shiftedPrimeProduct (h : ℕ) : ℕ :=
  ∏ p ∈ shiftedPrimes h, p

theorem shiftedPrimeProduct_pos (h : ℕ) : 0 < shiftedPrimeProduct h := by
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1.pos

theorem prime_dvd_shiftedPrimeProduct {p h : ℕ}
    (hp : p.Prime) (hh : 0 < h) (hdiv : p - 1 ∣ h) :
    p ∣ shiftedPrimeProduct h := by
  have hle : p - 1 ≤ h := Nat.le_of_dvd hh hdiv
  have hmem : p ∈ shiftedPrimes h :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hp.two_le; omega), hp, hdiv⟩
  exact Finset.dvd_prod_of_mem (fun p => p) hmem

/-- The elementary fixed-divisor bound, including the extra factor two. -/
theorem fixedDifferenceDivisor_dvd_shiftedPrimeBound {k j : ℕ} (hjk : j < k) :
    fixedDifferenceDivisor k j ∣
      2 * shiftedPrimeProduct (k - j) * (k - j) := by
  have hF : fixedDifferenceDivisor k j ≠ 0 := Nat.ne_of_gt (fixedDifferenceDivisor_pos hjk)
  have hH : k - j ≠ 0 := by omega
  have hD : shiftedPrimeProduct (k - j) ≠ 0 :=
    Nat.ne_of_gt (shiftedPrimeProduct_pos _)
  have h2D : 2 * shiftedPrimeProduct (k - j) ≠ 0 := mul_ne_zero (by decide) hD
  apply (Nat.factorization_le_iff_dvd hF (mul_ne_zero h2D hH)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpf : p ∣ fixedDifferenceDivisor k j
    · have hpd : p ∣ shiftedPrimeProduct (k - j) :=
        prime_dvd_shiftedPrimeProduct hp (by omega)
          (prime_sub_one_dvd_of_fixedDifferenceDivisor hp hjk.le hpf)
      have hDp : 1 ≤ (shiftedPrimeProduct (k - j)).factorization p :=
        Nat.succ_le_of_lt (hp.factorization_pos_of_dvd hD hpd)
      have hb := fixedDifferenceDivisor_factorization_le hp hjk
      have hprod :
          (2 * shiftedPrimeProduct (k - j) * (k - j)).factorization p =
          (2 : ℕ).factorization p + (shiftedPrimeProduct (k - j)).factorization p +
            (k - j).factorization p := by
        simp only [Nat.factorization_mul h2D hH,
          Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hD, Finsupp.add_apply]
      rw [hprod]
      by_cases hp2 : p = 2
      · subst p
        rw [Nat.prime_two.factorization_self]
        change (fixedDifferenceDivisor k j).factorization 2 ≤
          2 + (k - j).factorization 2 at hb
        omega
      · simp only [ite_eq_right hp2] at hb
        omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hpf]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem reductionModulus_dvd_shiftedPrimeBound (k d : ℕ) (hd : d < k) :
    reductionModulus k d ∣
      ∏ i ∈ Finset.range d,
        2 * shiftedPrimeProduct (k - (i + 1)) * (k - (i + 1)) := by
  apply (reductionModulus_dvd_fixedProduct k d hd).trans
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact fixedDifferenceDivisor_dvd_shiftedPrimeBound (by
    have := Finset.mem_range.mp hi
    omega)

end Erdos345
