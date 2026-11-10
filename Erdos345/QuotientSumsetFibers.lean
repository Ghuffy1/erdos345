import Erdos345.AdditiveProjection
import Erdos345.QuotientFiberBounds

namespace Erdos345

open scoped Classical Pointwise

/-- A lower bound on each occupied quotient-class fiber of an integer
sumset. It combines the coset deficit bound with ordered sumset growth. -/
theorem quotient_sumset_fiber_bound {ι G : Type*} [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset ℕ) (f : ℕ →+ G) (H : AddSubgroup G) [DecidableEq (G ⧸ H)]
    (b : ι → G ⧸ H)
    (hb : ∀ i ∈ I, b i ∈ ((A i).image f).image (QuotientAddGroup.mk : G → G ⧸ H)) :
    (∑ i ∈ I, ((A i).image f).card) + I.card * Nat.card H + 1 ≤
      ((∑ i ∈ I, A i).filter (fun n => QuotientAddGroup.mk (f n) = ∑ i ∈ I, b i)).card + I.card +
        ∑ i ∈ I, (((A i).image f).image (QuotientAddGroup.mk : G → G ⧸ H)).card * Nat.card H := by
  classical
  have heach (i : ι) (hi : i ∈ I) :
      ((A i).image f).card + Nat.card H ≤
        ((A i).filter (fun n => QuotientAddGroup.mk (f n) = b i)).card +
          (((A i).image f).image (QuotientAddGroup.mk : G → G ⧸ H)).card * Nat.card H := by
    have hd := quotient_fiber_defect_bound H ((A i).image f) (b i) (hb i hi)
    have hl := fiber_card_le_preimage_card (A i) f (QuotientAddGroup.mk : G → G ⧸ H) (b i)
    exact hd.trans (Nat.add_le_add_right hl _)
  have hsum := Finset.sum_le_sum heach
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hsum
  have hb' (i : ι) (hi : i ∈ I) :
      b i ∈ (A i).image ((QuotientAddGroup.mk' H).comp f) := by
    change b i ∈ (A i).image (fun n => QuotientAddGroup.mk (f n))
    have hh := hb i hi
    rw [Finset.image_image] at hh
    exact hh
  have hc := sumset_fiber_card_bound I A ((QuotientAddGroup.mk' H).comp f) b hb'
  change (∑ i ∈ I, ((A i).filter (fun n => QuotientAddGroup.mk (f n) = b i)).card) + 1 ≤
    ((∑ i ∈ I, A i).filter (fun n => QuotientAddGroup.mk (f n) = ∑ i ∈ I, b i)).card + I.card at hc
  omega

theorem quotient_sumset_fiber_bound_of_mem {ι G : Type*} [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset ℕ) (f : ℕ →+ G) (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (c : G ⧸ H)
    (hc : c ∈ ((∑ i ∈ I, A i).image f).image (QuotientAddGroup.mk : G → G ⧸ H)) :
    (∑ i ∈ I, ((A i).image f).card) + I.card * Nat.card H + 1 ≤
      ((∑ i ∈ I, A i).filter (fun n => QuotientAddGroup.mk (f n) = c)).card + I.card +
        ∑ i ∈ I, (((A i).image f).image (QuotientAddGroup.mk : G → G ⧸ H)).card * Nat.card H := by
  classical
  have hci : c ∈ ∑ i ∈ I, ((A i).image f).image (QuotientAddGroup.mk' H) := by
    rw [← image_indexed_sumset I (fun i => (A i).image f) (QuotientAddGroup.mk' H),
      ← image_indexed_sumset I A f]
    exact hc
  change c ∈ ((∑ i ∈ I, ((A i).image f).image (QuotientAddGroup.mk' H) : Finset (G ⧸ H)) : Set (G ⧸ H)) at hci
  rw [Finset.coe_sum, Set.mem_finsetSum] at hci
  obtain ⟨b, hb, hsum⟩ := hci
  have h := quotient_sumset_fiber_bound I A f H b (fun i hi => hb hi)
  rw [hsum] at h
  exact h

end Erdos345
