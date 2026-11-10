import Erdos345.OddDilationGenerator

namespace Erdos345

theorem prime_not_dvd_pred {p : ℕ} (hp : p.Prime) : ¬p ∣ p - 1 := by
  exact Nat.not_dvd_of_pos_of_lt (by have := hp.one_lt; omega) (by have := hp.pos; omega)

/-- The exact odd-prime lifting formula for the generator constructed above. -/
theorem generator_power_sub_one_factorization
    {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 < g) (hpg : ¬p ∣ g)
    (hclass : ∀ n : ℕ, p ∣ g ^ n - 1 ↔ p - 1 ∣ n)
    (hbase : (g ^ (p - 1) - 1).factorization p = 1)
    {h : ℕ} (hh : 0 < h) :
    (g ^ h - 1).factorization p = if p - 1 ∣ h then 1 + h.factorization p else 0 := by
  by_cases hd : p - 1 ∣ h
  · rw [ite_eq_left hd]
    obtain ⟨t, ht⟩ := hd
    have ht0 : t ≠ 0 := by intro hz; rw [hz, mul_zero] at ht; omega
    have hpred : p - 1 ≠ 0 := by have := hp.one_lt; omega
    have hNZ : g ^ h - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt
      (one_lt_pow₀ hg (Nat.ne_of_gt hh)))
    have hNZbase : g ^ (p - 1) - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt
      (one_lt_pow₀ hg hpred))
    have hodd : Odd p := Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left hp2)
    have hlift := Nat.emultiplicity_pow_sub_pow hp hodd (x := g ^ (p - 1)) (y := 1)
      ((hclass (p - 1)).mpr dvd_rfl) (fun hd => hpg (hp.dvd_of_dvd_pow hd)) t
    rw [one_pow, ← pow_mul, ← ht,
      ← factorization_cast_eq_emultiplicity hp hNZ,
      ← factorization_cast_eq_emultiplicity hp hNZbase,
      ← factorization_cast_eq_emultiplicity hp ht0, hbase] at hlift
    have heq : (g ^ h - 1).factorization p = 1 + t.factorization p := by
      exact_mod_cast hlift
    rw [heq]
    congr 1
    rw [ht, Nat.factorization_mul hpred ht0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_pred hp), zero_add]
  · rw [ite_eq_right hd]
    exact Nat.factorization_eq_zero_of_not_dvd ((hclass h).not.mpr hd)

theorem dilationDifference_odd_factorization
    {p g k j L : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 < g) (hpg : ¬p ∣ g)
    (hclass : ∀ n : ℕ, p ∣ g ^ n - 1 ↔ p - 1 ∣ n)
    (hbase : (g ^ (p - 1) - 1).factorization p = 1)
    (hj : j < k) (hL : 0 < L) :
    (dilationDifference g k j L).factorization p =
      if p - 1 ∣ (k - j) * L then 1 + (k - j).factorization p + L.factorization p else 0 := by
  have hdiff : k - j ≠ 0 := by omega
  have hL0 := Nat.ne_of_gt hL
  have hlen : 0 < (k - j) * L := Nat.mul_pos (by omega) hL
  have hNZ : g ^ ((k - j) * L) - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt
    (one_lt_pow₀ hg (Nat.ne_of_gt hlen)))
  rw [dilationDifference_factor hj.le, Nat.factorization_mul
    (pow_ne_zero _ (by omega : g ≠ 0)) hNZ, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun hd => hpg (hp.dvd_of_dvd_pow hd)), zero_add,
    generator_power_sub_one_factorization hp hp2 hg hpg hclass hbase hlen,
    Nat.factorization_mul hdiff hL0, Finsupp.add_apply, add_assoc]

theorem generator_coprime {p g : ℕ} (hp : p.Prime) (hpg : ¬p ∣ g) : g.Coprime p :=
  (hp.coprime_iff_not_dvd.mpr hpg).symm

theorem odd_generator_prime_power_period {p g : ℕ}
    (hp : p.Prime) (hpg : ¬p ∣ g) (a : ℕ) :
    Nat.ModEq (p ^ (a + 1)) (g ^ (p ^ a * (p - 1))) 1 := by
  simpa only [Nat.totient_prime_pow_succ hp] using
    Nat.ModEq.pow_totient ((generator_coprime hp hpg).pow_right (a + 1))

theorem generator_prime_power_period_factorization {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p ^ a * (p - 1)).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
    (by have := hp.one_lt; omega : p - 1 ≠ 0), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_pred hp), add_zero]
  simp only [Nat.factorization_pow, Finsupp.nsmul_apply, hp.factorization_self,
    nsmul_eq_mul, mul_one, Nat.cast_id]

end Erdos345
