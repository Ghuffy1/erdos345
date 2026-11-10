import Erdos345.QuotientSumsetFibers
import Erdos345.StabilizerQuotientCard

namespace Erdos345

open scoped Classical Pointwise

theorem stabilized_sumset_fiber_bound {ι G : Type*} [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : Finset ι) (A : ι → Finset ℕ) (f : ℕ →+ G) (R : Finset G)
    [DecidableEq (G ⧸ AddAction.stabilizer G (R : Set G))]
    (hR : R.Nonempty) (himage : R = (∑ i ∈ I, A i).image f)
    (c : G ⧸ AddAction.stabilizer G (R : Set G))
    (hc : c ∈ R.image (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G))) :
    (∑ i ∈ I, ((A i).image f).card) +
        I.card * Nat.card (AddAction.stabilizer G (R : Set G)) + 1 ≤
      ((∑ i ∈ I, A i).filter (fun n => QuotientAddGroup.mk (f n) = c)).card +
        I.card + ∑ i ∈ I, ((A i).image f + R.addStab).card := by
  classical
  have hc' : c ∈ ((∑ i ∈ I, A i).image f).image
      (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G)) := by
    rw [← himage]
    exact hc
  have hb := quotient_sumset_fiber_bound_of_mem I A f (AddAction.stabilizer G (R : Set G)) c hc'
  have heq : (∑ i ∈ I, (((A i).image f).image
      (QuotientAddGroup.mk : G → G ⧸ AddAction.stabilizer G (R : Set G))).card *
        Nat.card (AddAction.stabilizer G (R : Set G))) =
      ∑ i ∈ I, ((A i).image f + R.addStab).card := by
    apply Finset.sum_congr rfl
    intro i hi
    exact stabilizer_quotient_saturation_card R ((A i).image f) hR
  rw [heq] at hb
  exact hb

end Erdos345
