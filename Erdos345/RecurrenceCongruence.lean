import Erdos345.RecurrenceExtension
import Mathlib.Data.ZMod.Basic

namespace Erdos345

open Finset Polynomial

/-- A recurrence with a unit endpoint has unique values from its initial block.
The square-one formulation works in rings with zero divisors as well. -/
theorem zero_of_recurrence_initial {R : Type*} [CommRing R]
    (p : R[X]) (D : ℕ) (hdegree : p.natDegree ≤ D) (hunit : p.coeff D ^ 2 = 1)
    (f : ℕ → R) (hrec : shiftAction p f = 0) (hinit : ∀ n < D, f n = 0) :
    f = 0 := by
  funext n
  change f n = 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < D
    · exact hinit n hn
    have hDn : D ≤ n := Nat.le_of_not_gt hn
    have hr := congrFun hrec (n - D)
    rw [shiftAction_sum_of_degree_lt p f (by omega : p.natDegree < D + 1),
      sum_range_succ, Nat.sub_add_cancel hDn] at hr
    have hs : (∑ i ∈ range D, p.coeff i * f (n - D + i)) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hij : n - D + i < n := by have := mem_range.mp hi; omega
      rw [ih _ hij, mul_zero]
    rw [hs, zero_add] at hr
    change p.coeff D * f n = 0 at hr
    calc
      f n = p.coeff D ^ 2 * f n := by rw [hunit, one_mul]
      _ = p.coeff D * (p.coeff D * f n) := by ring
      _ = 0 := by rw [hr, mul_zero]

theorem eq_of_recurrence_initial {R : Type*} [CommRing R]
    (p : R[X]) (D : ℕ) (hdegree : p.natDegree ≤ D) (hunit : p.coeff D ^ 2 = 1)
    (f g : ℕ → R) (hf : shiftAction p f = 0) (hg : shiftAction p g = 0)
    (hinit : ∀ n < D, f n = g n) : f = g := by
  have hr : shiftAction p (f - g) = 0 := by rw [map_sub, hf, hg, sub_self]
  have hz := zero_of_recurrence_initial p D hdegree hunit (f - g) hr
    (fun n hn => by simp [hinit n hn])
  exact sub_eq_zero.mp hz

/-- Integer recurrence extensions preserve congruence to any sequence satisfying
the same recurrence modulo q. This does not assume q is prime. -/
theorem recurrence_congruence (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (q : ℕ) (f g : ℕ → ℤ) (hf : shiftAction p f = 0)
    (hg : ∀ n, (q : ℤ) ∣ shiftAction p g n)
    (hinit : ∀ n < p.natDegree, (q : ℤ) ∣ f n - g n) :
    ∀ n, (q : ℤ) ∣ f n - g n := by
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  have hfmap : shiftAction (p.map φ) (fun n => φ (f n)) = 0 := by
    funext n
    rw [shiftAction_map]
    have hn := congrFun hf n
    rw [hn]
    simp
  have hgmap : shiftAction (p.map φ) (fun n => φ (g n)) = 0 := by
    funext n
    rw [shiftAction_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hg n)
  have hunitmap : (p.map φ).coeff p.natDegree ^ 2 = 1 := by
    rw [coeff_map, coeff_natDegree, ← map_pow, hunit, map_one]
  have hsame := eq_of_recurrence_initial (p.map φ) p.natDegree natDegree_map_le hunitmap
    (fun n => φ (f n)) (fun n => φ (g n)) hfmap hgmap (fun n hn => by
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hinit n hn)
      change φ (f n - g n) = 0 at hz
      rw [map_sub] at hz
      exact sub_eq_zero.mp hz)
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  change φ (f n - g n) = 0
  rw [map_sub, congrFun hsame n, sub_self]

noncomputable def generatedRecurrence (p : ℤ[X])
    (init : Fin p.natDegree → ℤ) : ℕ → ℤ :=
  (polynomialRecurrence p).mkSol init

theorem generatedRecurrence_solution (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (init : Fin p.natDegree → ℤ) : shiftAction p (generatedRecurrence p init) = 0 :=
  (polynomialRecurrence_iff p hunit _).mp ((polynomialRecurrence p).is_sol_mkSol init)

theorem generatedRecurrence_initial (p : ℤ[X]) (init : Fin p.natDegree → ℤ)
    (i : Fin p.natDegree) : generatedRecurrence p init i = init i :=
  (polynomialRecurrence p).mkSol_eq_init init i

theorem generated_power_congruence (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (q k : ℕ) (hpower : ∀ n, (q : ℤ) ∣ shiftAction p (fun j : ℕ => (j : ℤ) ^ k) n) :
    ∀ n, (q : ℤ) ∣ generatedRecurrence p (fun i => (i : ℤ) ^ k) n - (n : ℤ) ^ k := by
  apply recurrence_congruence p hunit q _ _ (generatedRecurrence_solution p hunit _) hpower
  intro n hn
  have hinit := generatedRecurrence_initial p (fun i => (i : ℤ) ^ k) ⟨n, hn⟩
  simpa only [hinit, sub_self] using (dvd_zero (q : ℤ))

end Erdos345
