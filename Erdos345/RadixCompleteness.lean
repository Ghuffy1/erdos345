import Erdos345.Prouhet
import Erdos345.TailCompletion
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Ring.Parity

/-!
Classical completeness from equal sums of powers. The proof uses base 2^k:
the odd bases encode one digit and doubling separates all later digits. This
formalizes the radix part of Sprague's argument, with a Prouhet construction
providing the required equal sums.
-/

namespace Erdos345

open Finset

structure OddPowerPacket (k : ℕ) where
  total : ℕ
  total_pos : 0 < total
  bases : ℕ → Finset ℕ
  positive_odd : ∀ i < 2 ^ k, ∀ b ∈ bases i, 0 < b ∧ Odd b
  disjoint : ∀ i < 2 ^ k, ∀ j < 2 ^ k, i ≠ j → Disjoint (bases i) (bases j)
  sum_eq : ∀ i < 2 ^ k, ∑ b ∈ bases i, b ^ k = total

theorem exists_oddPowerPacket (k : ℕ) : Nonempty (OddPowerPacket k) := by
  let : NeZero (2 ^ k) := ⟨pow_ne_zero k (by decide)⟩
  obtain ⟨s, hs, F, hpos, hdis, hsum⟩ := exists_disjoint_odd_equal_powers (2 ^ k) k
  refine ⟨⟨s, hs, fun i => F (i : ZMod (2 ^ k)), ?_, ?_, ?_⟩⟩
  · intro i _ b hb
    exact hpos _ b hb
  · intro i hi j hj hij
    apply hdis
    intro heq
    have hv := congrArg ZMod.val heq
    simp only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hv
    exact hij hv
  · intro i _
    exact hsum _

theorem OddPowerPacket.base_le_total {k : ℕ} (P : OddPowerPacket k) (hk : 0 < k)
    {i b : ℕ} (hi : i < 2 ^ k) (hb : b ∈ P.bases i) : b ≤ P.total := by
  have hle : b ^ k ≤ ∑ a ∈ P.bases i, a ^ k :=
    single_le_sum (f := fun a => a ^ k) (fun _ _ => Nat.zero_le _) hb
  rw [P.sum_eq i hi] at hle
  exact (le_self_pow (by have := (P.positive_odd i hi b hb).1; omega) (Nat.ne_of_gt hk)).trans hle

noncomputable def OddPowerPacket.digitBases {k : ℕ} (P : OddPowerPacket k) (r : ℕ) :
    Finset ℕ := (range r).biUnion P.bases

theorem OddPowerPacket.digit_properties {k : ℕ} (P : OddPowerPacket k) (hk : 0 < k)
    {r : ℕ} (hr : r ≤ 2 ^ k) :
    (∀ b ∈ P.digitBases r, 0 < b ∧ Odd b ∧ b ≤ P.total) ∧
      ∑ b ∈ P.digitBases r, b ^ k = r * P.total := by
  constructor
  · intro b hb
    obtain ⟨i, hi, hb⟩ := mem_biUnion.mp hb
    have hiB : i < 2 ^ k := (mem_range.mp hi).trans_le hr
    exact ⟨(P.positive_odd i hiB b hb).1, (P.positive_odd i hiB b hb).2,
      P.base_le_total hk hiB hb⟩
  · rw [OddPowerPacket.digitBases, sum_biUnion]
    · simpa only [card_range] using
        (sum_const_nat (s := range r) (m := P.total)
          (fun i hi => P.sum_eq i ((mem_range.mp hi).trans_le hr)))
    · intro i hi j hj hij
      exact P.disjoint i ((mem_range.mp hi).trans_le hr)
        j ((mem_range.mp hj).trans_le hr) hij

/-- The odd bases are bounded; even bases may be arbitrarily large. -/
def oddControlledRepresentation (k s m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ b ∈ S, 0 < b ∧ (Odd b → b ≤ s)) ∧ ∑ b ∈ S, b ^ k = m

theorem oddControlledRepresentation_zero (k s : ℕ) : oddControlledRepresentation k s 0 := by
  exact ⟨∅, by simp, by simp⟩

theorem oddControlledRepresentation_scaled_add {k s m t : ℕ}
    (h : oddControlledRepresentation k s m) {D : Finset ℕ}
    (hD : ∀ b ∈ D, 0 < b ∧ Odd b ∧ b ≤ s) (hDt : ∑ b ∈ D, b ^ k = t) :
    oddControlledRepresentation k s (2 ^ k * m + t) := by
  classical
  obtain ⟨S, hS, hs⟩ := h
  let T := S.image (fun b => 2 * b)
  have hT : ∀ b ∈ T, 0 < b ∧ ¬ Odd b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact ⟨Nat.mul_pos (by decide) (hS a ha).1,
      Nat.not_odd_iff_even.mpr ⟨a, by omega⟩⟩
  have hdis : Disjoint T D := by
    apply disjoint_left.mpr
    intro b hb hd
    exact (hT b hb).2 (hD b hd).2.1
  refine ⟨T ∪ D, ?_, ?_⟩
  · intro b hb
    rcases mem_union.mp hb with hb | hb
    · exact ⟨(hT b hb).1, fun ho => False.elim ((hT b hb).2 ho)⟩
    · exact ⟨(hD b hb).1, fun _ => (hD b hb).2.2⟩
  · rw [sum_union hdis, hDt]
    congr 1
    rw [show T = S.image (fun b => 2 * b) from rfl, sum_image]
    · simp_rw [mul_pow]
      rw [← mul_sum, hs]
    · intro a _ b _ heq
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

/-- Every multiple of a packet total is represented, with its odd bases bounded
by that same total. Higher radix digits use only even bases. -/
theorem OddPowerPacket.represents_multiples {k : ℕ} (P : OddPowerPacket k)
    (hk : 0 < k) (m : ℕ) : oddControlledRepresentation k P.total (m * P.total) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      simpa only [zero_mul] using oddControlledRepresentation_zero k P.total
    have hB : 1 < 2 ^ k := Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide)
    have hq : m / 2 ^ k < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hB
    have hr : m % 2 ^ k ≤ 2 ^ k := (Nat.mod_lt m (by positivity)).le
    obtain ⟨hD, hsD⟩ := P.digit_properties hk hr
    have hrep := oddControlledRepresentation_scaled_add (ih _ hq) hD hsD
    have heq : 2 ^ k * (m / 2 ^ k * P.total) + m % 2 ^ k * P.total = m * P.total := by
      calc
        _ = (m % 2 ^ k + 2 ^ k * (m / 2 ^ k)) * P.total := by ring
        _ = _ := by rw [Nat.mod_add_div]
    rwa [heq] at hrep

def correctionBase (s i : ℕ) : ℕ := 2 * (s * (i + 1)) + 1

theorem correctionBase_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (correctionBase s) := by
  intro i j h
  have hprod : s * (i + 1) = s * (j + 1) := by
    dsimp only [correctionBase] at h
    omega
  have := Nat.eq_of_mul_eq_mul_left hs hprod
  omega

theorem correctionBase_odd_large (s i : ℕ) :
    Odd (correctionBase s i) ∧ s < correctionBase s i := by
  have hle : s ≤ s * (i + 1) := by
    calc
      s = s * 1 := by simp
      _ ≤ s * (i + 1) := Nat.mul_le_mul_left s (by omega)
  exact ⟨⟨s * (i + 1), rfl⟩, by dsimp [correctionBase]; omega⟩

def correctionSum (k s r : ℕ) : ℕ := ∑ i ∈ range r, correctionBase s i ^ k

noncomputable def correctionSet (s r : ℕ) : Finset ℕ :=
  (range r).image (correctionBase s)

theorem correctionSum_eq_set {s : ℕ} (hs : 0 < s) (k r : ℕ) :
    ∑ b ∈ correctionSet s r, b ^ k = correctionSum k s r := by
  classical
  rw [correctionSet, sum_image]
  · rfl
  · intro _ _ _ _ h
    exact correctionBase_injective hs h

theorem correctionSum_mono (k s : ℕ) {r t : ℕ} (hrt : r ≤ t) :
    correctionSum k s r ≤ correctionSum k s t := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono hrt)
  intro i _ _
  exact Nat.zero_le _

theorem correctionSum_modEq (k s r : ℕ) : Nat.ModEq s (correctionSum k s r) r := by
  have hbase (i : ℕ) : Nat.ModEq s (correctionBase s i) 1 := by
    dsimp only [Nat.ModEq, correctionBase]
    simp [Nat.add_mod, Nat.mul_mod]
  have hsum := Nat.ModEq.sum (s := range r) (fun i _ => (hbase i).pow k)
  simpa only [correctionSum, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one,
    Nat.cast_id] using hsum

/-- A packet of equal odd-power sums gives an explicit eventual threshold. -/
theorem OddPowerPacket.threshold {k : ℕ} (P : OddPowerPacket k) (hk : 0 < k) :
    correctionSum k P.total P.total ∈ thresholds (kthPowers k) := by
  intro m hm
  let r := m % P.total
  have hrs : r ≤ P.total := (Nat.mod_lt m P.total_pos).le
  have hcm : correctionSum k P.total r ≤ m := (correctionSum_mono k P.total hrs).trans hm
  have hcong : Nat.ModEq P.total (correctionSum k P.total r) m :=
    (correctionSum_modEq k P.total r).trans (Nat.mod_modEq m P.total)
  obtain ⟨q, hq⟩ := hcong.dvd'
  obtain ⟨S, hS, hs⟩ := P.represents_multiples hk q
  have hdis : Disjoint S (correctionSet P.total r) := by
    apply disjoint_left.mpr
    intro b hb hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    have hlarge := correctionBase_odd_large P.total i
    exact (Nat.not_lt_of_ge ((hS _ hb).2 hlarge.1)) hlarge.2
  apply (represented_iff_mem_subsetSums hk).mp
  refine ⟨S ∪ correctionSet P.total r, ?_, ?_⟩
  · intro b hb
    rcases mem_union.mp hb with hb | hb
    · exact (hS b hb).1
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact lt_trans P.total_pos (correctionBase_odd_large P.total i).2
  · rw [sum_union hdis, hs, correctionSum_eq_set P.total_pos]
    have hq' : q * P.total = m - correctionSum k P.total r := by
      rw [Nat.mul_comm, ← hq]
    rw [hq', Nat.sub_add_cancel hcm]

/-- Unconditional classical completeness for every positive exponent. -/
theorem exists_least_powerThreshold (k : ℕ) (hk : 0 < k) :
    ∃ b : ℕ, IsLeast (thresholds (kthPowers k)) b := by
  obtain ⟨P⟩ := exists_oddPowerPacket k
  exact exists_least_threshold_of_threshold (P.threshold hk)

noncomputable def leastPowerThreshold (k : ℕ) : ℕ := by
  classical
  exact if hk : 0 < k then Nat.find (exists_least_powerThreshold k hk) else 0

theorem leastPowerThreshold_spec (k : ℕ) (hk : 0 < k) :
    IsLeast (thresholds (kthPowers k)) (leastPowerThreshold k) := by
  classical
  rw [leastPowerThreshold, dite_eq_left hk]
  exact Nat.find_spec (exists_least_powerThreshold k hk)

/-- With existence now discharged, only the analytic inversion statement remains
as a premise here. This conditional lemma is not the main theorem. -/
theorem intended_of_late_powerThreshold_inversions
    (hinv : ∀ B : ℕ, ∃ j k : ℕ,
      B ≤ j ∧ j ≤ k ∧ leastPowerThreshold k < leastPowerThreshold j) :
    IntendedStatement :=
  intended_of_thresholds_and_late_inversions leastPowerThreshold leastPowerThreshold_spec hinv

end Erdos345
