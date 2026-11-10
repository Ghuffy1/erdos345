import Erdos345.ShiftedPrimeBound
import Mathlib.Combinatorics.Pigeonhole

namespace Erdos345

theorem shifted_product_fiber_card_le (P : Finset (ℕ × ℕ)) (n : ℕ) (hn : 0 < n)
    (hprime : ∀ z ∈ P, z.2.Prime) :
    (P.filter (fun z => z.1 * (z.2 - 1) = n)).card ≤ (shiftedPrimes n).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro z hz
    obtain ⟨hzP, hprod⟩ := Finset.mem_filter.mp hz
    have hp := hprime z hzP
    have hd : z.2 - 1 ∣ n := ⟨z.1, by nlinarith [hprod]⟩
    have hle := Nat.le_of_dvd hn hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hp.two_le; omega), hp, hd⟩
  · intro z hz w hw heq
    obtain ⟨hzP, hzprod⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwP, hwprod⟩ := Finset.mem_filter.mp hw
    have hp := (hprime z hzP).two_le
    apply Prod.ext
    · have he := hzprod.trans hwprod.symm
      rw [← heq] at he
      exact Nat.eq_of_mul_eq_mul_right (by omega) he
    · exact heq

/-- A finite form of the shifted-prime double-counting argument.
The abundance of the input pairs is a genuine premise, not asserted here. -/
theorem shifted_prime_spike_of_pair_count (P : Finset (ℕ × ℕ)) (K X C : ℕ)
    (hK : 0 < K)
    (hP : ∀ z ∈ P, 0 < z.1 ∧ z.1 ≤ X ∧ z.2.Prime ∧ z.2 ≤ X ∧ K ∣ z.1 * (z.2 - 1))
    (hcount : (X * X / K) * C < P.card) :
    ∃ n : ℕ, K ≤ n ∧ n ≤ X * X ∧ K ∣ n ∧ C < (shiftedPrimes n).card := by
  classical
  let f : ℕ × ℕ → ℕ := fun z => z.1 * (z.2 - 1) / K
  have hmap : ∀ z ∈ P, f z ∈ Finset.Icc 1 (X * X / K) := by
    intro z hz
    obtain ⟨hm0, hmX, hp, hpX, hd⟩ := hP z hz
    have hp1 : 0 < z.2 - 1 := by have := hp.two_le; omega
    have hprod0 := Nat.mul_pos hm0 hp1
    have hprodX : z.1 * (z.2 - 1) ≤ X * X :=
      Nat.mul_le_mul hmX ((Nat.sub_le _ _).trans hpX)
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hprod0 hd) hK,
      Nat.div_le_div_right hprodX⟩
  have hcard : (Finset.Icc 1 (X * X / K)).card * C < P.card := by simpa using hcount
  obtain ⟨v, hv, hvcount⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) hmap hcard
  let n := v * K
  have hKn : K ≤ n := by
    have hv1 := (Finset.mem_Icc.mp hv).1
    dsimp only [n]
    nlinarith
  have hnX : n ≤ X * X := by
    dsimp only [n]
    exact (Nat.mul_le_mul_right K (Finset.mem_Icc.mp hv).2).trans (Nat.div_mul_le_self _ _)
  have hn0 : 0 < n := hK.trans_le hKn
  have hfiber : P.filter (fun z => f z = v) ⊆ P.filter (fun z => z.1 * (z.2 - 1) = n) := by
    intro z hz
    obtain ⟨hzP, hfv⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzP, ?_⟩
    have hd := Nat.div_mul_cancel (hP z hzP).2.2.2.2
    change f z * K = z.1 * (z.2 - 1) at hd
    rw [hfv] at hd
    exact hd.symm
  have hprime : ∀ z ∈ P, z.2.Prime := fun z hz => (hP z hz).2.2.1
  refine ⟨n, hKn, hnX, ⟨v, by dsimp only [n]; ring⟩, ?_⟩
  exact hvcount.trans_le ((Finset.card_le_card hfiber).trans (shifted_product_fiber_card_le P n hn0 hprime))

end Erdos345
