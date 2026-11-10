import Erdos345.ModularAnnihilatorTransfer
import Erdos345.LocalScaling

namespace Erdos345

open Finset Polynomial

noncomputable def primaryOrders (S : Finset ℕ) (p : ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun n => ∃ a : ℕ, n = p ^ a)

noncomputable def nonprimaryOrders (S : Finset ℕ) (p : ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun n => ¬∃ a : ℕ, n = p ^ a)

theorem mem_primaryOrders (S : Finset ℕ) (p n : ℕ) :
    n ∈ primaryOrders S p ↔ n ∈ S ∧ ∃ a : ℕ, n = p ^ a := by
  classical
  exact mem_filter

theorem mem_nonprimaryOrders (S : Finset ℕ) (p n : ℕ) :
    n ∈ nonprimaryOrders S p ↔ n ∈ S ∧ ¬∃ a : ℕ, n = p ^ a := by
  classical
  exact mem_filter

theorem cyclotomicProduct_primary_split (S : Finset ℕ) (m : ℕ → ℕ) (p : ℕ) :
    cyclotomicProduct S m =
      cyclotomicProduct (primaryOrders S p) m * cyclotomicProduct (nonprimaryOrders S p) m := by
  classical
  symm
  exact prod_filter_mul_prod_filter_not S (fun n => ∃ a : ℕ, n = p ^ a)
    (fun n => (cyclotomic n ℤ) ^ m n)

theorem nonprimaryOrders_exclude_primePowers (S : Finset ℕ) (p n : ℕ)
    (hn : n ∈ nonprimaryOrders S p) : n ≠ 1 ∧ ∀ a : ℕ, n ≠ p ^ (a + 1) := by
  have hnot := ((mem_nonprimaryOrders S p n).mp hn).2
  constructor
  · intro h
    exact hnot ⟨0, by simpa using h⟩
  · intro a h
    exact hnot ⟨a + 1, h⟩

/-- Only the root-one and p-power factors matter modulo p^e. -/
theorem primary_power_annihilator (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ) (hp : p.Prime)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct (primaryOrders S p) m) (fun j : ℕ => (j : ℤ) ^ k) n := by
  apply remove_nonprimary_cyclotomic_factors (cyclotomicProduct (primaryOrders S p) m)
    (nonprimaryOrders S p) m p e k hp
    (fun n hn => nonprimaryOrders_exclude_primePowers S p n hn)
  intro n
  rw [← cyclotomicProduct_primary_split]
  exact hglobal n

theorem primary_local_scaling_bound (S : Finset ℕ) (m : ℕ → ℕ) (p e k : ℕ) (hp : p.Prime)
    (hm : ∀ n ∈ S, m n ≤ k)
    (hglobal : ∀ n, ((p ^ e : ℕ) : ℤ) ∣
      shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n) :
    (p - 1) * e ≤ ∑ n ∈ primaryOrders S p, if n = 1 then
      3 * m n + (p - 1) * (Nat.log p k + 1) else
      (p - 1) * ((Nat.log p n + 2) * m n + Nat.log p k + 1) := by
  apply local_scaling_multiplicity_bound (primaryOrders S p) m p e k hp
  · intro n hn
    exact ((mem_primaryOrders S p n).mp hn).2
  · intro n hn
    exact hm n ((mem_primaryOrders S p n).mp hn).1
  · exact primary_power_annihilator S m p e k hp hglobal

theorem rational_error_local_scaling_bound (S : Finset ℕ) (m : ℕ → ℕ)
    (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X]) (q u k : ℕ) (hq : 0 < q) (hu : u.Coprime q)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hphase : ∀ n : ℕ, f n + (g n : ℚ) = P.eval (n : ℚ))
    (hscale : ∀ n, (z n : ℚ) = (q : ℚ) * f n)
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (p e : ℕ) (hp : p.Prime) (hpeq : p ^ e ∣ q) (hm : ∀ n ∈ S, m n ≤ k) :
    (p - 1) * e ≤ ∑ n ∈ primaryOrders S p, if n = 1 then
      3 * m n + (p - 1) * (Nat.log p k + 1) else
      (p - 1) * ((Nat.log p n + 2) * m n + Nat.log p k + 1) := by
  have hglobal := rational_error_annihilator_mod_power S m f g z P q u k hq hu hminimal hphase hscale hPmod
  have hdiv : ((p ^ e : ℕ) : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpeq
  exact primary_local_scaling_bound S m p e k hp hm (fun n => hdiv.trans (hglobal n))

end Erdos345
