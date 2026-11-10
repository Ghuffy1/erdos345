import Erdos345.PrimaryAnnihilator

namespace Erdos345

open Finset Polynomial

theorem iteratedDifference_add {R : Type*} [Sub R] (f : ℕ → R) (a b : ℕ) :
    iteratedDifference (a + b) f = iteratedDifference b (iteratedDifference a f) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change difference (iteratedDifference (a + b) f) =
      difference (iteratedDifference b (iteratedDifference a f))
    exact congrArg difference ih

theorem difference_annihilator_reduction (q k h : ℕ) (hh : 0 < h)
    (hann : ∀ n, (q : ℤ) ∣ iteratedDifference h (fun j : ℕ => (j : ℤ) ^ k) n) :
    q ∣ reductionModulus k (h - 1) := by
  rw [dvd_reductionModulus_iff]
  intro j hj
  have hhj : h ≤ j := by omega
  have h := dvd_iteratedDifference (q : ℤ) (iteratedDifference h (fun n : ℕ => (n : ℤ) ^ k))
    hann (j - h) 0
  rw [← iteratedDifference_add, Nat.add_sub_of_le hhj, iteratedDifference_power_zero] at h
  exact_mod_cast h

theorem zeroth_difference_modulus_one (q k : ℕ)
    (hann : ∀ n, (q : ℤ) ∣ iteratedDifference 0 (fun j : ℕ => (j : ℤ) ^ k) n) : q = 1 := by
  have h := hann 1
  simp only [iteratedDifference, Nat.cast_one, one_pow] at h
  have hq : q ∣ 1 := by exact_mod_cast h
  exact Nat.dvd_one.mp hq

theorem primaryProduct_eq_rootOne (S : Finset ℕ) (m : ℕ → ℕ) (p : ℕ)
    (h1 : 1 ∈ S) (hzero : ∀ n ∈ primaryOrders S p, n ≠ 1 → m n = 0) :
    cyclotomicProduct (primaryOrders S p) m = (X - 1 : ℤ[X]) ^ m 1 := by
  classical
  rw [cyclotomicProduct, prod_eq_single 1]
  · simp only [cyclotomic_one]
  · intro n hn hn1
    rw [hzero n hn hn1, pow_zero]
  · intro hnot
    exact False.elim (hnot ((mem_primaryOrders S p 1).mpr ⟨h1, ⟨0, by simp⟩⟩))

theorem primary_multiplicity_zero_of_large_prime (S : Finset ℕ) (m : ℕ → ℕ)
    (p : ℕ) (hp : p.Prime) (T : ℝ) (hpT : T < p)
    (hbound : ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T) :
    ∀ n ∈ primaryOrders S p, n ≠ 1 → m n = 0 := by
  intro n hn hn1
  obtain ⟨a, ha⟩ := ((mem_primaryOrders S p n).mp hn).2
  have ha0 : a ≠ 0 := by intro h; subst a; simp only [pow_zero] at ha; exact hn1 ha
  have hpn : p ≤ n := by rw [ha]; exact le_self_pow₀ hp.one_lt.le ha0
  have hpnR : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have hb := hbound n hn hn1
  by_contra hm
  have hm1 : (1 : ℝ) ≤ m n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod := mul_le_mul_of_nonneg_left hm1 hn0
  nlinarith

theorem primary_rootOne_reduction (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ)
    (hp : p.Prime) (h1 : 1 ∈ S)
    (hzero : ∀ n ∈ primaryOrders S p, n ≠ 1 → m n = 0)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    (m 1 = 0 → p ^ e = 1) ∧
      (0 < m 1 → p ^ e ∣ reductionModulus k (m 1 - 1)) := by
  have hprimary := primary_power_annihilator S m p e k hp hglobal
  rw [primaryProduct_eq_rootOne S m p h1 hzero] at hprimary
  have hdiff : ∀ n, ((p ^ e : ℕ) : ℤ) ∣ iteratedDifference (m 1) (fun j : ℕ => (j : ℤ) ^ k) n := by
    intro n
    simpa only [shiftAction_difference_power] using hprimary n
  constructor
  · intro hm
    rw [hm] at hdiff
    exact zeroth_difference_modulus_one (p ^ e) k hdiff
  · intro hm
    exact difference_annihilator_reduction (p ^ e) k (m 1) hm hdiff

theorem large_prime_power_reduction (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ)
    (hp : p.Prime) (h1 : 1 ∈ S) (T : ℝ) (hpT : T < p)
    (hbound : ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    (m 1 = 0 → p ^ e = 1) ∧
      (0 < m 1 → p ^ e ∣ reductionModulus k (m 1 - 1)) :=
  primary_rootOne_reduction S m p e k hp h1
    (primary_multiplicity_zero_of_large_prime S m p hp T hpT hbound) hglobal

end Erdos345
