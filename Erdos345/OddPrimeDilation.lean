import Erdos345.OddDilationValuations

namespace Erdos345

open Finset

def oddPrimeDilationPeriod (_p n : ℕ) : ℕ := if n = 1 then 1 else n.totient

theorem oddPrimeDilationPeriod_one (p : ℕ) : oddPrimeDilationPeriod p 1 = 1 := by
  simp [oddPrimeDilationPeriod]

theorem oddPrimeDilationPeriod_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    oddPrimeDilationPeriod p (p ^ (a + 1)) = p ^ a * (p - 1) := by
  have hn : p ^ (a + 1) ≠ 1 := ne_of_gt (one_lt_pow₀ hp.one_lt (by omega))
  rw [oddPrimeDilationPeriod, ite_eq_right hn, Nat.totient_prime_pow_succ hp]

theorem oddPrimeDilationPeriod_pos {p n : ℕ} (hp : p.Prime)
    (hn : ∃ a : ℕ, n = p ^ a) : 0 < oddPrimeDilationPeriod p n := by
  obtain ⟨a, rfl⟩ := hn
  cases a with
  | zero => simp [oddPrimeDilationPeriod]
  | succ a =>
    rw [oddPrimeDilationPeriod_pow_succ hp]
    exact Nat.mul_pos (Nat.pow_pos hp.pos) (by have := hp.one_lt; omega)

theorem oddPrimeDilationPeriod_period {p g n : ℕ} (hp : p.Prime) (hpg : ¬p ∣ g)
    (hn : ∃ a : ℕ, n = p ^ a) :
    Nat.ModEq n (g ^ oddPrimeDilationPeriod p n) 1 := by
  obtain ⟨a, rfl⟩ := hn
  cases a with
  | zero => simp [oddPrimeDilationPeriod, Nat.ModEq, Nat.mod_one]
  | succ a =>
    rw [oddPrimeDilationPeriod_pow_succ hp]
    exact odd_generator_prime_power_period hp hpg a

theorem odd_dilation_root_one_sum
    {p g k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 < g) (hpg : ¬p ∣ g)
    (hclass : ∀ n : ℕ, p ∣ g ^ n - 1 ↔ p - 1 ∣ n)
    (hbase : (g ^ (p - 1) - 1).factorization p = 1) (hm : m ≤ k) :
    (∑ j ∈ range m, (dilationDifference g k j 1).factorization p) = rootOneWindow p k m := by
  rw [rootOneWindow, multipleWindow, sum_filter]
  apply sum_congr rfl
  intro j hj
  rw [dilationDifference_odd_factorization hp hp2 hg hpg hclass hbase
    (lt_of_lt_of_le (mem_range.mp hj) hm) (by decide)]
  simp only [Nat.mul_one, Nat.factorization_one, Finsupp.zero_apply, add_zero]

theorem odd_dilation_primary_sum
    {p g k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 < g) (hpg : ¬p ∣ g)
    (hclass : ∀ n : ℕ, p ∣ g ^ n - 1 ↔ p - 1 ∣ n)
    (hbase : (g ^ (p - 1) - 1).factorization p = 1) (hm : m ≤ k) (a : ℕ) :
    (∑ j ∈ range m, (dilationDifference g k j (p ^ a * (p - 1))).factorization p) =
      (a + 1) * m + valuationWindow p k m := by
  have hL : 0 < p ^ a * (p - 1) :=
    Nat.mul_pos (Nat.pow_pos hp.pos) (by have := hp.one_lt; omega)
  calc
    (∑ j ∈ range m, (dilationDifference g k j (p ^ a * (p - 1))).factorization p) =
        ∑ j ∈ range m, ((a + 1) + (k - j).factorization p) := by
      apply sum_congr rfl
      intro j hj
      have hd : p - 1 ∣ (k - j) * (p ^ a * (p - 1)) := ⟨(k - j) * p ^ a, by ring⟩
      rw [dilationDifference_odd_factorization hp hp2 hg hpg hclass hbase
        (lt_of_lt_of_le (mem_range.mp hj) hm) hL, ite_eq_left hd,
        generator_prime_power_period_factorization hp a]
      omega
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_const, card_range, smul_eq_mul, valuationWindow]
      ring

/-- Full odd-prime local scaling bound with no primitive-root existence premise. -/
theorem oddPrime_cyclotomic_multiplicity_bound
    (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : ∀ n ∈ S, ∃ a : ℕ, n = p ^ a) (hm : ∀ n ∈ S, m n ≤ k)
    (hpower : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    e ≤ ∑ n ∈ S, if n = 1 then rootOneWindow p k (m n) else
      Nat.log p n * m n + valuationWindow p k (m n) := by
  obtain ⟨g, hg, hpg, hclass, hbase⟩ := exists_odd_dilation_generator p hp hp2
  have hval := primePower_le_dilation_valuation_sum S m (oddPrimeDilationPeriod p)
    g p e k hp hg
    (fun n hn => by obtain ⟨a, rfl⟩ := hS n hn; exact Nat.pow_pos hp.pos)
    (fun n hn => oddPrimeDilationPeriod_pos hp (hS n hn)) hm
    (fun n hn => oddPrimeDilationPeriod_period hp hpg (hS n hn)) hpower
  apply hval.trans_eq
  apply sum_congr rfl
  intro n hn
  by_cases h1 : n = 1
  · rw [h1, ite_eq_left rfl, oddPrimeDilationPeriod_one]
    exact odd_dilation_root_one_sum hp hp2 hg hpg hclass hbase (hm 1 (h1 ▸ hn))
  · rw [ite_eq_right h1]
    obtain ⟨a, ha⟩ := hS n hn
    cases a with
    | zero => simp only [pow_zero] at ha; exact (h1 ha).elim
    | succ a =>
      have hmm : m (p ^ (a + 1)) ≤ k := by simpa only [ha] using hm n hn
      rw [ha, oddPrimeDilationPeriod_pow_succ hp,
        odd_dilation_primary_sum hp hp2 hg hpg hclass hbase hmm,
        Nat.log_pow hp.one_lt]

theorem oddPrime_cyclotomic_multiplicity_log_bound
    (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : ∀ n ∈ S, ∃ a : ℕ, n = p ^ a) (hm : ∀ n ∈ S, m n ≤ k)
    (hpower : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    (p - 1) * e ≤ ∑ n ∈ S,
      if n = 1 then 2 * m n + (p - 1) * (Nat.log p k + 1) else
        ((p - 1) * Nat.log p n + 1) * m n + (p - 1) * Nat.log p k := by
  have hb := Nat.mul_le_mul_left (p - 1)
    (oddPrime_cyclotomic_multiplicity_bound S m p e k hp hp2 hS hm hpower)
  rw [mul_sum] at hb
  apply hb.trans
  apply sum_le_sum
  intro n hn
  by_cases h1 : n = 1
  · simp only [ite_eq_left h1]
    exact rootOneWindow_scaled_le p k (m n) hp (hm n hn)
  · simp only [ite_eq_right h1]
    have hw := valuationWindow_scaled_le p k (m n) hp (hm n hn)
    nlinarith

end Erdos345
