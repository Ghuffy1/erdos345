import Erdos345.FixedDifferencePrimes
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos345

theorem fixedDifference_eq_nat_sub {k j a : ℕ} (ha : 1 ≤ a) (hjk : j ≤ k) :
    fixedDifference k j a = a ^ k - a ^ j := by
  have hpow : a ^ j ≤ a ^ k := Nat.pow_le_pow_right ha hjk
  have he : ((a ^ k - a ^ j : ℕ) : ℤ) = (a : ℤ) ^ k - (a : ℤ) ^ j := by
    rw [Int.natCast_sub hpow]
    simp only [Int.natCast_pow]
  rw [fixedDifference, ← he]
  exact Int.natAbs_natCast _

theorem nat_power_difference_factor (a : ℕ) {k j : ℕ} (hjk : j ≤ k) :
    a ^ k - a ^ j = a ^ j * (a ^ (k - j) - 1) := by
  rw [Nat.mul_sub_left_distrib, ← pow_add, mul_one]
  have he : j + (k - j) = k := by omega
  rw [he]

theorem prime_not_dvd_self_add_one {p : ℕ} (hp : p.Prime) : ¬p ∣ p + 1 := by
  intro h
  have hm := Nat.mod_eq_zero_of_dvd h
  simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hp.one_lt] at hm
  omega

theorem fixedDifferenceDivisor_dvd_factored_value (a : ℕ) {k j : ℕ}
    (ha : 1 ≤ a) (hjk : j ≤ k) :
    fixedDifferenceDivisor k j ∣ a ^ j * (a ^ (k - j) - 1) := by
  have hd := (dvd_fixedDifferenceDivisor_iff _ _ _ hjk).mp
    (dvd_rfl : fixedDifferenceDivisor k j ∣ fixedDifferenceDivisor k j) a
  rwa [fixedDifference_eq_nat_sub ha hjk, nat_power_difference_factor a hjk] at hd

theorem fixedDifferenceDivisor_odd_multiplicity {p k j : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hjk : j ≤ k) :
    emultiplicity p (fixedDifferenceDivisor k j) ≤
      1 + emultiplicity p (k - j) := by
  have hn := prime_not_dvd_self_add_one hp
  have hmult := emultiplicity_le_emultiplicity_of_dvd_right
    (a := p) (fixedDifferenceDivisor_dvd_factored_value (p + 1) (by omega) hjk)
  rw [hp.emultiplicity_mul, hp.emultiplicity_pow, emultiplicity_eq_zero.mpr hn,
    mul_zero, zero_add] at hmult
  have hlift := Nat.emultiplicity_pow_sub_pow hp hodd
    (x := p + 1) (y := 1) (by simp) hn (k - j)
  simp only [one_pow, Nat.add_sub_cancel, hp.emultiplicity_self] at hlift
  rwa [hlift] at hmult

theorem five_power_sub_one_multiplicity (h : ℕ) :
    emultiplicity 2 (5 ^ h - 1 : ℕ) = 2 + emultiplicity 2 h := by
  have hpos : 0 < (5 : ℕ) ^ h := pow_pos (by decide) h
  have hlift := Int.two_pow_sub_pow' (x := 5) (y := 1) h (by decide) (by decide)
  have hfour : emultiplicity (2 : ℤ) (4 : ℤ) = 2 := by
    simpa using
      (emultiplicity_pow_self_of_prime Int.prime_two 2)
  have hnat : emultiplicity (2 : ℤ) (h : ℤ) = emultiplicity (2 : ℕ) h :=
    Int.natCast_emultiplicity 2 h
  have hleft :
      emultiplicity (2 : ℤ) ((5 : ℤ) ^ h - 1) =
        emultiplicity 2 (5 ^ h - 1 : ℕ) := by
    rw [← Int.natCast_emultiplicity 2 (5 ^ h - 1)]
    congr 1
    rw [Int.natCast_sub (by omega : 1 ≤ (5 : ℕ) ^ h), Int.natCast_pow]
    rfl
  rw [one_pow, show (5 : ℤ) - 1 = 4 by decide, hfour,
    hnat, hleft] at hlift
  exact hlift

theorem fixedDifferenceDivisor_two_multiplicity {k j : ℕ} (hjk : j ≤ k) :
    emultiplicity 2 (fixedDifferenceDivisor k j) ≤
      2 + emultiplicity 2 (k - j) := by
  have hmult := emultiplicity_le_emultiplicity_of_dvd_right
    (a := (2 : ℕ)) (fixedDifferenceDivisor_dvd_factored_value 5 (by decide) hjk)
  rw [Nat.prime_two.emultiplicity_mul, Nat.prime_two.emultiplicity_pow,
    emultiplicity_eq_zero.mpr (by decide : ¬(2 : ℕ) ∣ 5), mul_zero, zero_add,
    five_power_sub_one_multiplicity] at hmult
  exact hmult

theorem factorization_cast_eq_emultiplicity {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (n.factorization p : ℕ∞) = emultiplicity p n := by
  rw [Nat.factorization_def n hp]
  exact padicValNat_eq_emultiplicity_of_ne_one hp.ne_one hn

theorem fixedDifferenceDivisor_factorization_le {p k j : ℕ}
    (hp : p.Prime) (hjk : j < k) :
    (fixedDifferenceDivisor k j).factorization p ≤
      (if p = 2 then 2 else 1) + (k - j).factorization p := by
  have hF := factorization_cast_eq_emultiplicity hp
    (Nat.ne_of_gt (fixedDifferenceDivisor_pos hjk))
  have hH := factorization_cast_eq_emultiplicity hp
    (by omega : k - j ≠ 0)
  by_cases ht : p = 2
  · subst p
    have hb := fixedDifferenceDivisor_two_multiplicity hjk.le
    rw [← hF, ← hH] at hb
    exact_mod_cast hb
  · have hodd : Odd p := Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left ht)
    have hb := fixedDifferenceDivisor_odd_multiplicity hp hodd hjk.le
    rw [← hF, ← hH] at hb
    simp only [ite_eq_right ht]
    exact_mod_cast hb

end Erdos345
