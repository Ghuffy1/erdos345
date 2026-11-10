import Erdos345.LargePrimeReduction

namespace Erdos345

open Finset

theorem primary_order_ge_prime (S : Finset ℕ) (p n : ℕ) (hp : p.Prime)
    (hn : n ∈ primaryOrders S p) (hn1 : n ≠ 1) : p ≤ n := by
  obtain ⟨a, ha⟩ := ((mem_primaryOrders S p n).mp hn).2
  have ha0 : a ≠ 0 := by intro h; subst a; simp only [pow_zero] at ha; exact hn1 ha
  rw [ha]
  exact le_self_pow₀ hp.one_lt.le ha0

theorem primaryOrders_card_le_log (S : Finset ℕ) (p N : ℕ) (hp : p.Prime)
    (hmax : ∀ n ∈ S, n ≤ N) : (primaryOrders S p).card ≤ Nat.log p N + 1 := by
  have hle : (primaryOrders S p).card ≤ (range (Nat.log p N + 1)).card := by
    apply card_le_card_of_injOn (Nat.log p)
    · intro n hn
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hmax n ((mem_primaryOrders S p n).mp hn).1)))
    · intro a ha b hb hab
      obtain ⟨i, hi⟩ := ((mem_primaryOrders S p a).mp ha).2
      obtain ⟨j, hj⟩ := ((mem_primaryOrders S p b).mp hb).2
      rw [hi, hj, Nat.log_pow hp.one_lt, Nat.log_pow hp.one_lt] at hab
      rw [hi, hj, hab]
  simpa only [card_range] using hle

/-- A finite, deliberately coarse local exponent estimate. Its loss is
polynomial in the two logarithms; no infinite-series estimate is assumed. -/
theorem primary_exponent_bound (S : Finset ℕ) (m : ℕ → ℕ) (p e k N : ℕ) (hp : p.Prime)
    (hmax : ∀ n ∈ S, n ≤ N) (hm : ∀ n ∈ S, m n ≤ k)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n)
    (T : ℝ) (hT : 0 ≤ T) (hroot : (m 1 : ℝ) ≤ T)
    (hbound : ∀ n ∈ primaryOrders S p, n ≠ 1 → (n : ℝ) * m n ≤ T) :
    (e : ℝ) ≤
      (((Nat.log p N : ℝ) + 1) * ((Nat.log p N : ℝ) + 5) * T) / ((p - 1 : ℕ) : ℝ) +
        ((Nat.log p N : ℝ) + 1) * ((Nat.log p k : ℝ) + 1) := by
  let A := Nat.log p N
  let W : ℝ := (Nat.log p k : ℝ) + 1
  let b : ℝ := (p - 1 : ℕ)
  let H : ℝ := ((A : ℝ) + 5) * T + b * W
  have hb : 0 < b := by dsimp [b]; exact_mod_cast (by have := hp.two_le; omega : 0 < p - 1)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hlocal := primary_local_scaling_bound S m p e k hp hm hglobal
  have hlocalR : b * (e : ℝ) ≤ ∑ n ∈ primaryOrders S p, if n = 1 then
      3 * (m n : ℝ) + b * W else b * (((Nat.log p n : ℝ) + 2) * (m n : ℝ) + W) := by
    dsimp only [b, W]
    exact_mod_cast hlocal
  have hterm : ∀ n ∈ primaryOrders S p,
      (if n = 1 then 3 * (m n : ℝ) + b * W else
        b * (((Nat.log p n : ℝ) + 2) * (m n : ℝ) + W)) ≤ H := by
    intro n hn
    by_cases hn1 : n = 1
    · rw [ite_eq_left hn1, hn1]
      dsimp only [H]
      have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      nlinarith
    · rw [ite_eq_right hn1]
      have hpn : p ≤ n := primary_order_ge_prime S p n hp hn hn1
      have hbn : b ≤ (n : ℝ) := by
        dsimp [b]
        exact_mod_cast (Nat.sub_le p 1).trans hpn
      have hmul : b * (m n : ℝ) ≤ T :=
        (mul_le_mul_of_nonneg_right hbn (Nat.cast_nonneg _)).trans (hbound n hn hn1)
      have hlog : (Nat.log p n : ℝ) ≤ A := by
        exact_mod_cast Nat.log_mono_right (hmax n ((mem_primaryOrders S p n).mp hn).1)
      have hstep : ((Nat.log p n : ℝ) + 2) * (b * (m n : ℝ)) ≤ ((A : ℝ) + 2) * T := by
        exact (mul_le_mul_of_nonneg_left hmul (by positivity)).trans
          (mul_le_mul_of_nonneg_right (by linarith) hT)
      dsimp only [H]
      nlinarith
  have hsum : (∑ n ∈ primaryOrders S p, if n = 1 then
      3 * (m n : ℝ) + b * W else b * (((Nat.log p n : ℝ) + 2) * (m n : ℝ) + W)) ≤
        ((primaryOrders S p).card : ℝ) * H := by
    calc
      _ ≤ ∑ _n ∈ primaryOrders S p, H := sum_le_sum hterm
      _ = _ := by simp
  have hcard : ((primaryOrders S p).card : ℝ) ≤ (A : ℝ) + 1 := by
    exact_mod_cast primaryOrders_card_le_log S p N hp hmax
  have htotal : b * (e : ℝ) ≤ ((A : ℝ) + 1) * H :=
    (hlocalR.trans hsum).trans (mul_le_mul_of_nonneg_right hcard hH)
  have hbp : ((p - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hb
  calc
    (e : ℝ) ≤ (((A : ℝ) + 1) * H) / b := (le_div_iff₀ hb).mpr (by nlinarith)
    _ = _ := by
      dsimp [H, b, W, A]
      field_simp [hbp]

end Erdos345
