import Erdos345.ShiftedPrimeGcdClasses
import Mathlib.NumberTheory.PrimeCounting

namespace Erdos345

def primesOneMod (X d : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter (fun p => d ∣ p - 1)

def divisorPrimePairs (K X d : ℕ) : Finset (ℕ × ℕ) :=
  (gcdClass K X d).product (primesOneMod X d)

def selectedDivisorPairs (K X : ℕ) (D : Finset ℕ) : Finset (ℕ × ℕ) :=
  D.biUnion (divisorPrimePairs K X)

theorem gcd_classes_disjoint (K X d e : ℕ) (hK : 0 < K) (hd : d ∣ K) (he : e ∣ K)
    (hne : d ≠ e) : Disjoint (gcdClass K X d) (gcdClass K X e) := by
  apply Finset.disjoint_left.mpr
  intro m hmd hme
  have hdEq := (Finset.mem_filter.mp hmd).2
  have heEq := (Finset.mem_filter.mp hme).2
  have hquot : K / d = K / e := hdEq.symm.trans heEq
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hK
  have ha : 0 < K / d := Nat.div_pos (Nat.le_of_dvd hK hd) hd0
  have hprod : (K / d) * d = (K / d) * e := by
    rw [Nat.div_mul_cancel hd, hquot, Nat.div_mul_cancel he]
  exact hne (Nat.eq_of_mul_eq_mul_left ha hprod)

theorem divisor_prime_pairs_disjoint (K X d e : ℕ) (hK : 0 < K) (hd : d ∣ K) (he : e ∣ K)
    (hne : d ≠ e) : Disjoint (divisorPrimePairs K X d) (divisorPrimePairs K X e) := by
  apply Finset.disjoint_left.mpr
  intro z hzd hze
  have hmD := (Finset.mem_product.mp hzd).1
  have hmE := (Finset.mem_product.mp hze).1
  exact Finset.disjoint_left.mp (gcd_classes_disjoint K X d e hK hd he hne) hmD hmE

theorem selected_divisor_pairs_card_lower (K X : ℕ) (D : Finset ℕ) (hK : 0 < K)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ∣ K) :
    (∑ d ∈ D, (X / K) * d.totient * (primesOneMod X d).card) ≤
      (selectedDivisorPairs K X D).card := by
  classical
  have hdj : (D : Set ℕ).PairwiseDisjoint (divisorPrimePairs K X) := by
    intro d hd e he hne
    exact divisor_prime_pairs_disjoint K X d e hK (hD d hd).2 (hD e he).2 hne
  rw [selectedDivisorPairs, Finset.card_biUnion hdj]
  apply Finset.sum_le_sum
  intro d hd
  rw [divisorPrimePairs, Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul_right _ (gcd_class_card_lower K X d hK (hD d hd).2 (hD d hd).1)

theorem selected_divisor_pairs_valid (K X : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d ∣ K) :
    ∀ z ∈ selectedDivisorPairs K X D,
      0 < z.1 ∧ z.1 ≤ X ∧ z.2.Prime ∧ z.2 ≤ X ∧ K ∣ z.1 * (z.2 - 1) := by
  classical
  intro z hz
  obtain ⟨d, hd, hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨hm, hp⟩ := Finset.mem_product.mp hz
  obtain ⟨hmX, hmgcd⟩ := Finset.mem_filter.mp hm
  obtain ⟨hpX, hpdiv⟩ := Finset.mem_filter.mp hp
  have hmdiv : K / d ∣ z.1 := by
    rw [← hmgcd]
    exact Nat.gcd_dvd_left _ _
  have hprod := Nat.mul_dvd_mul hmdiv hpdiv
  rw [Nat.div_mul_cancel (hD d hd)] at hprod
  exact ⟨(Finset.mem_Icc.mp hmX).1, (Finset.mem_Icc.mp hmX).2,
    (Nat.mem_primesLE.mp hpX).2, (Nat.mem_primesLE.mp hpX).1, hprod⟩

/-- A finite prime-in-progressions criterion for a large shifted-prime divisor count. -/
theorem shifted_prime_spike_of_progression_counts (K X C : ℕ) (D : Finset ℕ) (hK : 0 < K)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ∣ K)
    (hcount : (X * X / K) * C < ∑ d ∈ D, (X / K) * d.totient * (primesOneMod X d).card) :
    ∃ n : ℕ, K ≤ n ∧ n ≤ X * X ∧ K ∣ n ∧ C < (shiftedPrimes n).card := by
  apply shifted_prime_spike_of_pair_count (selectedDivisorPairs K X D) K X C hK
  · exact selected_divisor_pairs_valid K X D (fun d hd => (hD d hd).2)
  · exact hcount.trans_le (selected_divisor_pairs_card_lower K X D hK hD)

end Erdos345
