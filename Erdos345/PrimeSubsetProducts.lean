import Erdos345.PrimeThetaLower
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.NumberTheory.Primorial

namespace Erdos345

/-- Squarefree divisors formed from exactly `r` of the primes up to `Y`. -/
def primeSubsetProducts (Y r : ℕ) : Finset ℕ :=
  ((Nat.primesLE Y).powersetCard r).image (fun s => ∏ p ∈ s, p)

theorem prime_product_injective (Y : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) ((Nat.primesLE Y).powerset : Set (Finset ℕ)) := by
  intro s hs t ht heq
  have hsP : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp hs) hp)
  have htP : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have h := congrArg Nat.primeFactors heq
  simpa only [Nat.primeFactors_prod hsP, Nat.primeFactors_prod htP] using h

theorem prime_subset_products_card (Y r : ℕ) :
    (primeSubsetProducts Y r).card = (Nat.primesLE Y).card.choose r := by
  rw [primeSubsetProducts, Finset.card_image_of_injOn]
  · exact Finset.card_powersetCard r (Nat.primesLE Y)
  · intro s hs t ht heq
    exact prime_product_injective Y
      (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1)
      (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp ht).1) heq

theorem prime_subset_products_valid (Y r : ℕ) (hr : 0 < r) :
    ∀ d ∈ primeSubsetProducts Y r,
      2 ≤ d ∧ d ∣ primorial Y ∧ d ≤ Y ^ r := by
  intro d hd
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hsY, hsr⟩ := Finset.mem_powersetCard.mp hs
  have hsP : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hsY hp)
  have hspos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hsP p hp).pos)
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hsne
  have hpdiv : p ∣ ∏ q ∈ s, q := Finset.dvd_prod_of_mem (fun q => q) hp
  refine ⟨(hsP p hp).two_le.trans (Nat.le_of_dvd hspos hpdiv), ?_, ?_⟩
  · rw [primorial_eq_prod_primesLE]
    exact Finset.prod_dvd_prod_of_subset s (Nat.primesLE Y) (fun p => p) hsY
  · calc
      (∏ p ∈ s, p) ≤ ∏ _p ∈ s, Y := Finset.prod_le_prod (fun p hp =>
        (Nat.mem_primesLE.mp (hsY hp)).1)
      _ = Y ^ r := by rw [Finset.prod_const, hsr]

theorem choose_lower_half (n r : ℕ) (h : 2 * r ≤ n) :
    (n : ℝ) ^ r / (2 ^ r * r.factorial) ≤ (n.choose r : ℝ) := by
  have hs : (n : ℝ) / 2 ≤ (n + 1 - r : ℕ) := by
    have he : n ≤ 2 * (n + 1 - r) := by omega
    have heR : (n : ℝ) ≤ 2 * (n + 1 - r : ℕ) := by exact_mod_cast he
    linarith
  calc
    (n : ℝ) ^ r / (2 ^ r * r.factorial) = ((n : ℝ) / 2) ^ r / r.factorial := by
      rw [div_pow]
      ring
    _ ≤ ((n + 1 - r : ℕ) : ℝ) ^ r / r.factorial :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs r) (by positivity)
    _ ≤ (n.choose r : ℝ) := Nat.pow_le_choose r n

theorem prime_count_sqrt_lower (Y : ℕ) (hY : 16384 ≤ Y) :
    Real.sqrt (Y : ℝ) ≤ (Nat.primesLE Y).card := by
  have hYR : (16384 : ℝ) ≤ Y := by exact_mod_cast hY
  have htheta := prime_theta_half_large Y hY
  have hpi := Chebyshev.theta_le_pi_mul_log Y
  have hlog := log_le_sqrt_large hYR
  have hs0 := Real.sqrt_nonneg (Y : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg Y)
  have hc0 : (0 : ℝ) ≤ Nat.primeCounting Y := Nat.cast_nonneg _
  by_contra h
  have hcard : (Nat.primesLE Y).card = Nat.primeCounting Y := by
    exact Nat.primesLE_card_eq_primeCounting Y
  rw [hcard] at h
  have hc : (Nat.primeCounting Y : ℝ) ≤ Real.sqrt (Y : ℝ) := le_of_lt (lt_of_not_ge h)
  have h1 := mul_le_mul_of_nonneg_left hlog hc0
  have h2 := mul_le_mul_of_nonneg_right hc hs0
  nlinarith only [htheta, hpi, h1, h2, hs2, hYR]

end Erdos345
