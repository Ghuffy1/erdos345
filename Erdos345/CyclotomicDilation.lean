import Erdos345.CyclotomicUnitFactors
import Erdos345.DilationMatrix
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

namespace Erdos345

open Finset Polynomial Matrix

/-- Coprime substitution preserves the original cyclotomic factor. -/
theorem cyclotomic_dvd_expand {R : Type*} [CommRing R]
    (n g : ℕ) (hg : 0 < g) (hcop : g.Coprime n) :
    cyclotomic n R ∣ expand R g (cyclotomic n R) := by
  induction g using Nat.strong_induction_on with
  | h g ih =>
    by_cases hg1 : g = 1
    · subst g
      rw [expand_one]
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
    obtain ⟨m, hgm⟩ := hpg
    have hmpos : 0 < m := by
      rw [hgm] at hg
      apply Nat.pos_of_ne_zero
      intro hm
      rw [hm, mul_zero] at hg
      omega
    have hmlt : m < g := by
      rw [hgm]
      nlinarith [hp.two_le]
    have hmdvd : m ∣ g := by rw [hgm]; exact dvd_mul_left m p
    have hmco : m.Coprime n := hcop.of_dvd_left hmdvd
    have hpco : p.Coprime n := hcop.of_dvd_left ⟨m, hgm⟩
    have hpn : ¬p ∣ n := (hp.coprime_iff_not_dvd).mp hpco
    have hprime : cyclotomic n R ∣ expand R p (cyclotomic n R) := by
      rw [cyclotomic_expand_eq_cyclotomic_mul hp hpn R]
      exact dvd_mul_left _ _
    have hmap := map_dvd (expand R p) (ih m hmlt hmpos hmco)
    have hresult := hprime.trans hmap
    simpa only [expand_expand, ← hgm] using hresult

theorem cyclotomicProduct_dvd_expand (S : Finset ℕ) (m : ℕ → ℕ) (g : ℕ)
    (hg : 0 < g) (hcop : ∀ n ∈ S, g.Coprime n) :
    cyclotomicProduct S m ∣ expand ℤ g (cyclotomicProduct S m) := by
  rw [cyclotomicProduct, map_prod]
  apply Finset.prod_dvd_prod_of_dvd
  intro n hn
  rw [map_pow]
  exact pow_dvd_pow_of_dvd (cyclotomic_dvd_expand n g hg (hcop n hn)) _

/-- Filtering a sampled sequence equals filtering the original sequence with
the substituted polynomial and then sampling. -/
theorem shiftAction_dilate {R : Type*} [CommRing R] (p : R[X]) (f : ℕ → R)
    (g n : ℕ) :
    shiftAction p (fun j => f (g * j)) n =
      shiftAction (expand R g p) f (g * n) := by
  symm
  calc
    shiftAction (expand R g p) f (g * n) =
        ∑ i ∈ range (p.natDegree + 1), p.coeff i * f (g * n + g * i) := by
      rw [shiftAction, expand_aeval, aeval_eq_sum_range]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, ← pow_mul, sequenceShift_pow]
    _ = shiftAction p (fun j => f (g * j)) n := by
      rw [shiftAction_sum]
      simp only [Nat.mul_add]

theorem dilation_preserves_recurrence {R : Type*} [CommRing R]
    (p : R[X]) (f : ℕ → R) (g : ℕ)
    (hdiv : p ∣ expand R g p) (hf : shiftAction p f = 0) :
    shiftAction p (fun n => f (g * n)) = 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hzero : shiftAction (expand R g p) f = 0 := by
    rw [hQ, mul_comm, shiftAction_mul, hf, shiftAction_zero_sequence]
  funext n
  rw [shiftAction_dilate]
  exact congrFun hzero (g * n)

theorem cyclotomic_dilation_preserves_recurrence
    (S : Finset ℕ) (m : ℕ → ℕ) (g : ℕ) (hg : 0 < g)
    (hcop : ∀ n ∈ S, g.Coprime n)
    (f : ℕ → ℤ) (hf : shiftAction (cyclotomicProduct S m) f = 0) :
    shiftAction (cyclotomicProduct S m) (fun n => f (g * n)) = 0 :=
  dilation_preserves_recurrence _ f g (cyclotomicProduct_dvd_expand S m g hg hcop) hf

/-- The actual integer sampling matrix is the dilation operator on the full
solution sequence whenever polynomial divisibility gives invariance. -/
theorem dilationMatrix_matches_sequence (p : ℤ[X]) (hunit : p.leadingCoeff ^ 2 = 1)
    (g : ℕ) (hdiv : p ∣ expand ℤ g p) (v : Fin p.natDegree → ℤ) (n : ℕ) :
    generatedRecurrence p (dilationMatrix p g *ᵥ v) n = generatedRecurrence p v (g * n) := by
  have hf := generatedRecurrence_solution p hunit v
  have hscaled := dilation_preserves_recurrence p (generatedRecurrence p v) g hdiv hf
  have hsame := eq_of_recurrence_initial p p.natDegree le_rfl
    (by simpa only [coeff_natDegree] using hunit)
    (generatedRecurrence p (dilationMatrix p g *ᵥ v))
    (fun j => generatedRecurrence p v (g * j))
    (generatedRecurrence_solution p hunit _) hscaled (fun j hj => by
      have hinit := generatedRecurrence_initial p (dilationMatrix p g *ᵥ v) ⟨j, hj⟩
      calc
        generatedRecurrence p (dilationMatrix p g *ᵥ v) j = (dilationMatrix p g *ᵥ v) ⟨j, hj⟩ := hinit
        _ = generatedRecurrence p v (g * j) := dilationMatrix_mulVec p g v ⟨j, hj⟩)
  exact congrFun hsame n

end Erdos345
