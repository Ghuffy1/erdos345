import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Lean.Elab.Tactic.Omega

/-!
Original problem: https://www.erdosproblems.com/345

Development module. This file fixes the intended statement and proves elementary
bridges. It does not claim to prove the full Erdős problem.
-/

namespace Erdos345

/-- Finite subset sums, including the empty sum. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ A ∧ n = ∑ b ∈ B, b}

/-- The set of values of positive integer k-th powers. -/
def kthPowers (k : ℕ) : Set ℕ :=
  {x | ∃ n : ℕ, 0 < n ∧ n ^ k = x}

/-- All thresholds, with the same inclusive convention as Formal Conjectures. -/
def thresholds (A : Set ℕ) : Set ℕ :=
  {m | ∀ n : ℕ, m ≤ n → n ∈ subsetSums A}

/-- Exact intended proposition; an unproved definition is not a proof. -/
def IntendedStatement : Prop :=
  {k : ℕ | 0 < k ∧ ∃ a b : ℕ,
    IsLeast (thresholds (kthPowers k)) a ∧
    IsLeast (thresholds (kthPowers (k + 1))) b ∧ b < a}.Infinite

theorem thresholds_upward {A : Set ℕ} {a b : ℕ}
    (ha : a ∈ thresholds A) (hab : a ≤ b) : b ∈ thresholds A := by
  intro n hn
  exact ha n (hab.trans hn)

theorem threshold_le_of_isLeast {A : Set ℕ} {a b : ℕ}
    (ha : IsLeast (thresholds A) a) (hb : b ∈ thresholds A) : a ≤ b :=
  ha.2 hb

theorem least_threshold_unique {A : Set ℕ} {a b : ℕ}
    (ha : IsLeast (thresholds A) a) (hb : IsLeast (thresholds A) b) : a = b :=
  le_antisymm (ha.2 hb.1) (hb.2 ha.1)

theorem isLeast_thresholds_one : IsLeast (thresholds (kthPowers 1)) 0 := by
  refine ⟨?_, fun m _ => Nat.zero_le m⟩
  intro n _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, by simp, by simp⟩
  · refine ⟨{n}, ?_, by simp⟩
    intro x hx
    have hxn : x = n := by simpa using hx
    exact ⟨n, hn, by simp [hxn]⟩

/-- Finite drops force monotonicity after some index. -/
theorem eventually_monotone_of_finite_drops (T : ℕ → ℕ)
    (hfin : {k : ℕ | T (k + 1) < T k}.Finite) :
    ∃ B : ℕ, MonotoneOn T (Set.Ici B) := by
  classical
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B + 1, monotoneOn_nat_Ici_of_le_succ ?_⟩
  intro n hn
  by_contra h
  have hd : n ∈ {k : ℕ | T (k + 1) < T k} := Nat.lt_of_not_ge h
  have : n ≤ B := hB hd
  omega

/-- Arbitrarily late inversions imply infinitely many adjacent strict drops.
This is the logical last step, conditional on its explicitly stated input. -/
theorem infinite_drops_of_late_inversions (T : ℕ → ℕ)
    (hinv : ∀ B : ℕ, ∃ j k : ℕ, B ≤ j ∧ j ≤ k ∧ T k < T j) :
    {k : ℕ | T (k + 1) < T k}.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := eventually_monotone_of_finite_drops T hfin
  obtain ⟨j, k, hBj, hjk, hlt⟩ := hinv B
  have hle : T j ≤ T k := hB hBj (hBj.trans hjk) hjk
  omega

/-- Removing index zero preserves infinitude, needed for positive exponents. -/
theorem infinite_positive_drops_of_late_inversions (T : ℕ → ℕ)
    (hinv : ∀ B : ℕ, ∃ j k : ℕ, B ≤ j ∧ j ≤ k ∧ T k < T j) :
    {k : ℕ | 0 < k ∧ T (k + 1) < T k}.Infinite := by
  have h := infinite_drops_of_late_inversions T hinv
  have hdiff := h.sdiff (Set.finite_singleton 0)
  apply hdiff.mono
  intro k hk
  exact ⟨Nat.pos_of_ne_zero (by simpa using hk.2), hk.1⟩

/-- A transparent assembly lemma. Its two premises are outstanding obligations,
not assumptions of the original Erdős problem. -/
theorem intended_of_thresholds_and_late_inversions (T : ℕ → ℕ)
    (hthreshold : ∀ k : ℕ, 0 < k → IsLeast (thresholds (kthPowers k)) (T k))
    (hinv : ∀ B : ℕ, ∃ j k : ℕ, B ≤ j ∧ j ≤ k ∧ T k < T j) :
    IntendedStatement := by
  apply (infinite_positive_drops_of_late_inversions T hinv).mono
  intro k hk
  exact ⟨hk.1, T k, T (k + 1), hthreshold k hk.1,
    hthreshold (k + 1) (Nat.succ_pos k), hk.2⟩

end Erdos345
