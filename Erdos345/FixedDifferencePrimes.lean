import Erdos345.FixedDifferenceDivisors
import Erdos345.FiniteObstruction
import Mathlib.RingTheory.IntegralDomain

namespace Erdos345

theorem prime_sub_one_dvd_of_fixedDifferenceDivisor {p k j : ℕ}
    (hp : p.Prime) (hjk : j ≤ k) (h : p ∣ fixedDifferenceDivisor k j) :
    p - 1 ∣ k - j := by
  let : Fact p.Prime := ⟨hp⟩
  have hvalues : ∀ n : ℕ, (n : ZMod p) ^ k = (n : ZMod p) ^ j := by
    intro n
    have hn := (dvd_fixedDifferenceDivisor_iff p k j hjk).mp h n
    have hz : (p : ℤ) ∣ (n : ℤ) ^ k - (n : ℤ) ^ j := Int.natCast_dvd.mpr hn
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) ^ k - (n : ℤ) ^ j) p).mpr hz
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have horder : orderOf g = p - 1 := by
    have ho := orderOf_eq_card_of_forall_mem_zpowers hg
    simpa only [Nat.card_units, Nat.card_zmod] using ho
  have hkg : g ^ k = g ^ j := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, ZMod.natCast_zmod_val] using
      hvalues (g : ZMod p).val
  have hpow : g ^ (k - j) = 1 := by
    apply mul_right_cancel (b := g ^ j)
    rw [← pow_add, Nat.sub_add_cancel hjk, one_mul]
    exact hkg
  rw [← horder]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

theorem prime_dvd_fixedDifferenceDivisor_of_sub_one_dvd {p k j : ℕ}
    (hp : p.Prime) (hj : 0 < j) (hjk : j ≤ k) (h : p - 1 ∣ k - j) :
    p ∣ fixedDifferenceDivisor k j := by
  apply (dvd_fixedDifferenceDivisor_iff p k j hjk).mpr
  intro n
  have hcore : (n : ZMod p) ^ (k - j + 1) = (n : ZMod p) := by
    have hc := (ZMod.natCast_eq_natCast_iff' (n ^ (k - j + 1)) n p).mpr
      (shifted_power_mod_prime hp h n)
    simpa only [Nat.cast_pow] using hc
  have hk : k = (j - 1) + (k - j + 1) := by omega
  have hj' : j = (j - 1) + 1 := by omega
  have hkpow : (n : ZMod p) ^ k =
      (n : ZMod p) ^ (j - 1) * (n : ZMod p) ^ (k - j + 1) := by
    exact (congrArg (fun a => (n : ZMod p) ^ a) hk).trans (pow_add _ _ _)
  have hjpow : (n : ZMod p) ^ j = (n : ZMod p) ^ (j - 1) * (n : ZMod p) := by
    have hh := congrArg (fun a => (n : ZMod p) ^ a) hj'
    simpa only [pow_add, pow_one] using hh
  have hsame : (n : ZMod p) ^ k = (n : ZMod p) ^ j := by
    rw [hkpow, hcore, ← hjpow]
  apply Int.natCast_dvd.mp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) ^ k - (n : ℤ) ^ j) p).mp
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, hsame, sub_self]

theorem prime_dvd_fixedDifferenceDivisor_iff {p k j : ℕ}
    (hp : p.Prime) (hj : 0 < j) (hjk : j ≤ k) :
    p ∣ fixedDifferenceDivisor k j ↔ p - 1 ∣ k - j :=
  ⟨prime_sub_one_dvd_of_fixedDifferenceDivisor hp hjk,
    prime_dvd_fixedDifferenceDivisor_of_sub_one_dvd hp hj hjk⟩

end Erdos345
