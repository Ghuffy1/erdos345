import Erdos345.WindowErrorHeight

namespace Erdos345

open Finset Polynomial

theorem integer_annihilator_of_rational_map (P : ℤ[X]) (f : ℕ → ℤ)
    (hf : shiftAction (P.map (Int.castRingHom ℚ)) (fun n => (f n : ℚ)) = 0) :
    shiftAction P f = 0 := by
  funext n
  have h := congrFun hf n
  change shiftAction (P.map (Int.castRingHom ℚ)) (fun n => (Int.castRingHom ℚ) (f n)) n = 0 at h
  rw [shiftAction_map] at h
  change ((shiftAction P f n : ℤ) : ℚ) = 0 at h
  change shiftAction P f n = 0
  exact_mod_cast h

theorem minimal_integer_cyclotomic_annihilates (S : Finset ℕ) (m : ℕ → ℕ) (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ))) :
    shiftAction (cyclotomicProduct S m) f = 0 := by
  apply integer_annihilator_of_rational_map
  rw [hminimal]
  exact minimalAnnihilator_annihilates _

/-- A pointwise integral congruence transfers an annihilator to the power
sequence. Coprimality cancels the numerator over the full residue ring. -/
theorem annihilator_transfer_to_power (P : ℤ[X]) (f : ℕ → ℤ)
    (hf : shiftAction P f = 0) (q u k : ℕ) (hu : u.Coprime q)
    (hcong : ∀ n, (q : ℤ) ∣ f n - (u : ℤ) * (n : ℤ) ^ k) :
    ∀ n, (q : ℤ) ∣ shiftAction P (fun j : ℕ => (j : ℤ) ^ k) n := by
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  have hmap : shiftAction (P.map φ) (fun n => φ (f n)) = 0 := by
    funext n
    simp only [shiftAction_map, congrFun hf n, Pi.zero_apply, map_zero]
  have hseq : (fun n => φ (f n)) = (u : ZMod q) • (fun n : ℕ => φ ((n : ℤ) ^ k)) := by
    funext n
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hcong n)
    change φ (f n - (u : ℤ) * (n : ℤ) ^ k) = 0 at h
    rw [map_sub, map_mul] at h
    simpa only [Pi.smul_apply, smul_eq_mul, φ, Int.coe_castRingHom, Int.cast_natCast] using sub_eq_zero.mp h
  rw [hseq, map_smul] at hmap
  have hunit : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime u q).mpr hu
  have hpower := hunit.smul_eq_zero.mp hmap
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  have h := congrFun hpower n
  rw [shiftAction_map] at h
  exact h

theorem integer_error_power_congruence (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X])
    (q u k : ℕ)
    (hphase : ∀ n : ℕ, f n + (g n : ℚ) = P.eval (n : ℚ))
    (hscale : ∀ n, (z n : ℚ) = (q : ℚ) * f n)
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k) :
    ∀ n, (q : ℤ) ∣ z n - (u : ℤ) * (n : ℤ) ^ k := by
  intro n
  obtain ⟨A, hA, hmod⟩ := hPmod n
  have heqQ : (A : ℚ) = (z n : ℚ) + (q : ℚ) * (g n : ℚ) := by
    rw [← hA, ← hphase n, hscale n]
    ring
  have heq : A = z n + (q : ℤ) * g n := by exact_mod_cast heqQ
  have h := dvd_sub hmod (dvd_mul_right (q : ℤ) (g n))
  rw [heq] at h
  convert h using 1
  ring

theorem rational_error_annihilator_mod_power (S : Finset ℕ) (m : ℕ → ℕ)
    (f : ℕ → ℚ) (g z : ℕ → ℤ) (P : ℚ[X]) (q u k : ℕ) (hq : 0 < q) (hu : u.Coprime q)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hphase : ∀ n : ℕ, f n + (g n : ℚ) = P.eval (n : ℚ))
    (hscale : ∀ n, (z n : ℚ) = (q : ℚ) * f n)
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k) :
    ∀ n, (q : ℤ) ∣ shiftAction (cyclotomicProduct S m) (fun j : ℕ => (j : ℤ) ^ k) n := by
  have hminz := integer_multiple_minimal_cyclotomic S m f z q hq hscale hminimal
  exact annihilator_transfer_to_power (cyclotomicProduct S m) z
    (minimal_integer_cyclotomic_annihilates S m z hminz) q u k hu
    (integer_error_power_congruence f g z P q u k hphase hscale hPmod)

end Erdos345
