import Erdos345.DilationValuations
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace Erdos345

theorem natCast_power_eq_one_iff_dvd_sub (g N n : ℕ) (hg : 1 ≤ g) :
    (g : ZMod N) ^ n = 1 ↔ N ∣ g ^ n - 1 := by
  rw [← sub_eq_zero, ← Nat.cast_pow, ← Nat.cast_one,
    ← Nat.cast_sub (one_le_pow₀ hg), ZMod.natCast_eq_zero_iff]

theorem odd_prime_lift_dvd {p g n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hg : 1 < g) (hpg : ¬p ∣ g) (hd : p ∣ g ^ n - 1) :
    p ^ 2 ∣ g ^ (n * p) - 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hNZ : g ^ n - 1 ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ hg hn))
    have hNP : g ^ (n * p) - 1 ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ hg (mul_ne_zero hn hp.ne_zero)))
    have hh := Nat.emultiplicity_pow_sub_pow hp hodd (x := g ^ n) (y := 1)
      hd (fun h => hpg (hp.dvd_of_dvd_pow h)) p
    rw [one_pow, ← pow_mul, hp.emultiplicity_self,
      ← factorization_cast_eq_emultiplicity hp hNZ,
      ← factorization_cast_eq_emultiplicity hp hNP] at hh
    have heq : (g ^ (n * p) - 1).factorization p = (g ^ n - 1).factorization p + 1 := by
      exact_mod_cast hh
    apply (hp.pow_dvd_iff_le_factorization hNP).mpr
    have h1 := (hp.dvd_iff_one_le_factorization hNZ).mp hd
    omega

/-- A primitive residue modulo p² gives the exact root-one congruence class
and valuation-one base needed for local dilation. Existence is proved from
cyclicity of the units; it is not an additional number-theoretic assumption. -/
theorem exists_odd_dilation_generator (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : ℕ, 1 < g ∧ ¬p ∣ g ∧
      (∀ n : ℕ, p ∣ g ^ n - 1 ↔ p - 1 ∣ n) ∧
      (g ^ (p - 1) - 1).factorization p = 1 := by
  classical
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcyclic := ZMod.isCyclic_units_of_prime_pow p hp hp2 2
  obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyclic
  let g : ℕ := (u : ZMod (p ^ 2)).val
  have hcast : (g : ZMod (p ^ 2)) = (u : ZMod (p ^ 2)) := ZMod.natCast_zmod_val _
  have ho : orderOf (g : ZMod (p ^ 2)) = p * (p - 1) := by
    have hi := orderOf_injective (Units.coeHom (ZMod (p ^ 2))) Units.coeHom_injective u
    change orderOf (u : ZMod (p ^ 2)) = orderOf u at hi
    rw [hcast, hi, hu,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa only [pow_one] using Nat.totient_prime_pow_succ hp 1
  have hgp2 : g.Coprime (p ^ 2) :=
    (ZMod.isUnit_iff_coprime g (p ^ 2)).mp (hcast.symm ▸ u.isUnit)
  have hgp : g.Coprime p := hgp2.coprime_dvd_right (dvd_pow_self p (by decide))
  have hpg : ¬p ∣ g := fun hd => hp.not_dvd_one
    (hgp.symm.dvd_of_dvd_mul_left (by simpa only [mul_one] using hd : p ∣ g * 1))
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hg : 1 < g := by
    by_contra h
    have hcases : g = 0 ∨ g = 1 := by omega
    rcases hcases with hz | h1
    · exact hpg (hz ▸ dvd_zero p)
    · rw [h1, Nat.cast_one, orderOf_one] at ho
      nlinarith
  have hodd : Odd p := Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left hp2)
  have horder (n : ℕ) : p ^ 2 ∣ g ^ n - 1 ↔ p * (p - 1) ∣ n := by
    rw [← natCast_power_eq_one_iff_dvd_sub g (p ^ 2) n hg.le,
      ← orderOf_dvd_iff_pow_eq_one, ho]
  have hfermat : Nat.ModEq p (g ^ (p - 1)) 1 := by
    simpa only [Nat.totient_prime hp] using Nat.ModEq.pow_totient hgp
  have hclass (n : ℕ) : p ∣ g ^ n - 1 ↔ p - 1 ∣ n := by
    constructor
    · intro hd
      have hd2 := odd_prime_lift_dvd hp hodd hg hpg hd
      have hmul := (horder (n * p)).mp hd2
      have hc : (p - 1) * p ∣ n * p := by simpa only [Nat.mul_comm p (p - 1)] using hmul
      exact (Nat.mul_dvd_mul_iff_right hp.pos).mp hc
    · rintro ⟨t, rfl⟩
      have ht := hfermat.pow t
      have hmod : Nat.ModEq p 1 (g ^ ((p - 1) * t)) := by
        simpa only [← pow_mul, one_pow] using ht.symm
      exact (Nat.modEq_iff_dvd' (one_le_pow₀ hg.le)).mp hmod
  have hNZ : g ^ (p - 1) - 1 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ hg (by omega)))
  have hlow : 1 ≤ (g ^ (p - 1) - 1).factorization p :=
    (hp.dvd_iff_one_le_factorization hNZ).mp ((hclass (p - 1)).mpr dvd_rfl)
  have hupper : ¬2 ≤ (g ^ (p - 1) - 1).factorization p := by
    intro h
    have hd := (horder (p - 1)).mp ((hp.pow_dvd_iff_le_factorization hNZ).mpr h)
    have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hd
    nlinarith
  exact ⟨g, hg, hpg, hclass, by omega⟩

end Erdos345
