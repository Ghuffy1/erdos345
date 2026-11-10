import Erdos345.QuotientRegionGrowth
import Erdos345.StabilizedFiberBound
import Erdos345.PeriodicLiftingArithmetic

namespace Erdos345

open scoped Classical Pointwise

set_option maxHeartbeats 400000 in
/-- Periodic lifting from a strict expansion in the stabilizer quotient.
No analytic or arithmetic progression hypothesis is hidden in this lemma. -/
theorem periodic_sumset_lifting {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty) (A : ι → Finset ℕ)
    (hA : ∀ i ∈ I, (A i).Nonempty) (T : Finset ℕ) (q : ℕ)
    (hq : 0 < q) [NeZero q]
    (hT : T ⊆ ∑ i ∈ I, A i)
    (htrans : T.image (fun n => n + q) ⊆ ∑ i ∈ I, A i)
    (hsat : naturalResidueImage T q + (naturalResidueImage (∑ i ∈ I, A i) q).addStab ⊆
      naturalResidueImage (∑ i ∈ I, A i) q)
    (hnew :
      let R := naturalResidueImage (∑ i ∈ I, A i) q
      let H := AddAction.stabilizer (ZMod q) (R : Set (ZMod q))
      (naturalResidueImage T q).image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H) ⊂
        R.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H)) :
    T.card + (∑ i ∈ I, (naturalResidueImage (A i) q).card) + 1 ≤
      (∑ i ∈ I, A i).card + I.card := by
  classical
  let S := ∑ i ∈ I, A i
  let X := fun i => naturalResidueImage (A i) q
  let R := naturalResidueImage S q
  let P := naturalResidueImage T q
  let H := AddAction.stabilizer (ZMod q) (R : Set (ZMod q))
  let π := (QuotientAddGroup.mk' H)
  let Rq := R.image π
  let Pq := P.image π
  let C := Rq \ Pq
  let d := Nat.card H
  let h := I.card
  let x := ∑ i ∈ I, (X i).card
  let z := ∑ i ∈ I, (X i + R.addStab).card
  let f := Nat.castAddMonoidHom (ZMod q)
  let φ := π.comp f
  have hR : R.Nonempty := by
    exact Finset.image_nonempty.mpr (indexed_sumset_nonempty I A hA)
  have hRsum : R = ∑ i ∈ I, X i := image_indexed_sumset I A f
  have hRcard : R.card = Rq.card * d := stabilizer_quotient_self_card R hR
  have hPcard : (P + R.addStab).card = Pq.card * d :=
    (stabilizer_quotient_saturation_card R P hR).symm
  have hz : z ≤ Rq.card * d + (h - 1) * d := by
    have hb := multiple_kneser I hI X (fun i hi => Finset.image_nonempty.mpr (hA i hi))
    dsimp only at hb
    rw [← hRsum] at hb
    change z ≤ R.card + (h - 1) * R.addStab.card at hb
    rw [hRcard, ← stabilizer_natCard R hR] at hb
    exact hb
  have hglobal : T.card + R.card ≤ S.card := endpoint_extension_card_growth T S q hq hT htrans
  change T.card + x + 1 ≤ S.card + h
  by_cases hbad : R.card + h ≤ x
  · have hnew' : Pq ⊂ Rq := hnew
    have hC : C.Nonempty := Finset.sdiff_nonempty.mpr hnew'.not_superset
    have ht : 0 < C.card := Finset.card_pos.mpr hC
    have hpr : Pq.card + C.card = Rq.card := by
      have hb := Finset.card_sdiff_add_card_eq_card hnew'.subset
      change C.card + Pq.card = Rq.card at hb
      omega
    have hbad' : Rq.card * d + h ≤ x := by simpa only [hRcard] using hbad
    have hh : 0 < h := Finset.card_pos.mpr hI
    have hh' : h - 1 + 1 = h := by omega
    have hz' : z + d ≤ Rq.card * d + h * d := by nlinarith [hz]
    have hsz : h + z ≤ x + h * d + 1 := by omega
    let k := x + h * d + 1 - (h + z)
    have hk : k + (h + z) = x + h * d + 1 := Nat.sub_add_cancel hsz
    have hphi : S.image φ = Rq := by
      change S.image (fun n : ℕ => QuotientAddGroup.mk (n : ZMod q)) =
        (S.image (fun n : ℕ => (n : ZMod q))).image π
      rw [Finset.image_image]
      rfl
    let O := S.filter (fun n => φ n ∈ Pq)
    let U := S.filter (fun n => φ n ∈ C)
    have hpart : O.card + U.card = S.card := by
      have hb := fiber_partition_card S φ Pq
      rw [hphi] at hb
      exact hb
    have hold : T.card + Pq.card * d ≤ O.card := by
      have hb := quotient_old_region_growth S T q hq hR hT htrans hsat
      change T.card + (P + R.addStab).card ≤ O.card at hb
      rw [hPcard] at hb
      exact hb
    have hfiber : ∀ c ∈ C, k ≤ (S.filter (fun n => φ n = c)).card := by
      intro c hc
      have hcr : c ∈ R.image (QuotientAddGroup.mk : ZMod q → ZMod q ⧸ H) := by
        change c ∈ Rq
        exact (Finset.mem_sdiff.mp hc).1
      have hb := stabilized_sumset_fiber_bound I A f R hR rfl c hcr
      change x + h * d + 1 ≤ (S.filter (fun n => φ n = c)).card + h + z at hb
      omega
    have hU : C.card * k ≤ U.card := by
      rw [show U.card = ∑ c ∈ C, (S.filter (fun n => φ n = c)).card from
        fiber_region_card_eq_sum S φ C]
      calc
        C.card * k = ∑ _c ∈ C, k := by simp
        _ ≤ _ := Finset.sum_le_sum hfiber
    apply periodic_lifting_arithmetic h d x z Pq.card Rq.card C.card k T.card S.card
      hh ht hpr hz hbad' hk
    omega
  · omega

end Erdos345
