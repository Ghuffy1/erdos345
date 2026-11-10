import Erdos345.ShiftedPrimePairCounting
import Mathlib.Data.Nat.Totient

namespace Erdos345

def gcdClass (K X d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun m => Nat.gcd m K = K / d)

theorem gcd_class_embedding (K d j u : ℕ) (hK : 0 < K) (hd : d ∣ K)
    (hd2 : 2 ≤ d) (hu : u < d) (hcop : d.Coprime u) :
    j * K < j * K + (K / d) * u ∧
      j * K + (K / d) * u < (j + 1) * K ∧
      Nat.gcd (j * K + (K / d) * u) K = K / d := by
  have hd0 : 0 < d := by omega
  have ha : 0 < K / d := Nat.div_pos (Nat.le_of_dvd hK hd) hd0
  have hu0 : 0 < u := by
    by_contra hz
    have heq : u = 0 := by omega
    simp only [heq, Nat.coprime_zero_right] at hcop
    omega
  have hKd : (K / d) * d = K := Nat.div_mul_cancel hd
  have hres : (K / d) * u < K := by
    calc
      _ < (K / d) * d := Nat.mul_lt_mul_of_pos_left hu ha
      _ = _ := hKd
  refine ⟨by nlinarith [Nat.mul_pos ha hu0], by nlinarith, ?_⟩
  have hm : j * K + (K / d) * u = (K / d) * (u + j * d) := by nlinarith [hKd]
  calc
    _ = Nat.gcd ((K / d) * (u + j * d)) ((K / d) * d) := by rw [hm, hKd]
    _ = (K / d) * Nat.gcd (u + j * d) d := Nat.gcd_mul_left _ _ _
    _ = K / d := by rw [Nat.gcd_add_mul_right_left, hcop.symm.gcd_eq_one, Nat.mul_one]

theorem gcd_class_card_lower (K X d : ℕ) (hK : 0 < K) (hd : d ∣ K) (hd2 : 2 ≤ d) :
    (X / K) * d.totient ≤ (gcdClass K X d).card := by
  classical
  let R := (Finset.range d).filter (fun u => d.Coprime u)
  let T := (Finset.range (X / K)).product R
  let f : ℕ × ℕ → ℕ := fun z => z.1 * K + (K / d) * z.2
  have props : ∀ z ∈ T, z.1 * K < f z ∧ f z < (z.1 + 1) * K ∧ Nat.gcd (f z) K = K / d := by
    intro z hz
    have hu := (Finset.mem_product.mp hz).2
    exact gcd_class_embedding K d z.1 z.2 hK hd hd2
      (Finset.mem_range.mp (Finset.mem_filter.mp hu).1) (Finset.mem_filter.mp hu).2
  have maps : Set.MapsTo f T (gcdClass K X d) := by
    intro z hz
    obtain ⟨hlo, hhi, hg⟩ := props z hz
    have hj : z.1 < X / K := Finset.mem_range.mp (Finset.mem_product.mp hz).1
    have hx : (z.1 + 1) * K ≤ X :=
      (Nat.mul_le_mul_right K (show z.1 + 1 ≤ X / K by omega)).trans (Nat.div_mul_le_self _ _)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hg⟩
  have inj : (T : Set (ℕ × ℕ)).InjOn f := by
    intro z hz w hw heq
    obtain ⟨hzlo, hzhi, _⟩ := props z hz
    obtain ⟨hwlo, hwhi, _⟩ := props w hw
    have hj : z.1 = w.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs := Nat.mul_le_mul_right K (show z.1 + 1 ≤ w.1 by omega)
        omega
      · have hs := Nat.mul_le_mul_right K (show w.1 + 1 ≤ z.1 by omega)
        omega
    apply Prod.ext hj
    have ha : 0 < K / d := Nat.div_pos (Nat.le_of_dvd hK hd) (by omega)
    change z.1 * K + (K / d) * z.2 = w.1 * K + (K / d) * w.2 at heq
    rw [hj] at heq
    exact Nat.eq_of_mul_eq_mul_left ha (Nat.add_left_cancel heq)
  have hc := Finset.card_le_card_of_injOn f maps inj
  have hT : T.card = (X / K) * d.totient := by
    dsimp only [T]
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
    rfl
  rw [hT] at hc
  exact hc

end Erdos345
