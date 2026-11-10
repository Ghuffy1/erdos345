import Erdos345.Representations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos345

/-- A representation whose positive bases are all at most B. -/
def representedUpTo (k B m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ b ∈ S, 0 < b ∧ b ≤ B) ∧ ∑ b ∈ S, b ^ k = m

theorem representedUpTo_represented {k B m : ℕ} (h : representedUpTo k B m) :
    represented k m := by
  obtain ⟨S, hS, hs⟩ := h
  exact ⟨S, fun b hb => (hS b hb).1, hs⟩

theorem representedUpTo_mono {k B C m : ℕ} (h : representedUpTo k B m)
    (hBC : B ≤ C) : representedUpTo k C m := by
  obtain ⟨S, hS, hs⟩ := h
  exact ⟨S, fun b hb => ⟨(hS b hb).1, (hS b hb).2.trans hBC⟩, hs⟩

theorem representedUpTo_add_next {k B m : ℕ} (h : representedUpTo k B m) :
    representedUpTo k (B + 1) (m + (B + 1) ^ k) := by
  classical
  obtain ⟨S, hS, hs⟩ := h
  have hnot : B + 1 ∉ S := by
    intro hb
    have := (hS (B + 1) hb).2
    omega
  refine ⟨insert (B + 1) S, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨Nat.succ_pos B, le_rfl⟩
    · exact ⟨(hS b hb).1, (hS b hb).2.trans (Nat.le_succ B)⟩
  · rw [Finset.sum_insert hnot, hs, Nat.add_comm]

/-- Every integer in an inclusive interval has a representation using bases ≤ B. -/
def representedInterval (k B a L : ℕ) : Prop :=
  ∀ m : ℕ, a ≤ m → m ≤ a + L → representedUpTo k B m

/-- The interval joins its translate when the new coin is at most L+1. -/
theorem representedInterval_add_next {k B a L : ℕ}
    (h : representedInterval k B a L) (hcoin : (B + 1) ^ k ≤ L + 1) :
    representedInterval k (B + 1) a (L + (B + 1) ^ k) := by
  intro m hma hmL
  by_cases hmold : m ≤ a + L
  · exact representedUpTo_mono (h m hma hmold) (Nat.le_succ B)
  · have hcm : (B + 1) ^ k ≤ m := by omega
    have hlo : a ≤ m - (B + 1) ^ k := by omega
    have hhi : m - (B + 1) ^ k ≤ a + L := by omega
    have hnew := representedUpTo_add_next (h (m - (B + 1) ^ k) hlo hhi)
    simpa only [Nat.sub_add_cancel hcm] using hnew

/-- An elementary upper Bernoulli estimate with all denominators cleared. -/
theorem succ_pow_mul_sub_le (k b : ℕ) (hk : k ≤ b) :
    (b + 1) ^ k * (b - k) ≤ b ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega : k ≤ b)
    have hstep : b - k = b - (k + 1) + 1 := by omega
    have hfactor : (b + 1) * (b - (k + 1)) ≤ b * (b - k) := by
      rw [hstep]
      nlinarith [Nat.sub_le b (k + 1)]
    calc
      (b + 1) ^ (k + 1) * (b - (k + 1)) =
          (b + 1) ^ k * ((b + 1) * (b - (k + 1))) := by ring
      _ ≤ (b + 1) ^ k * (b * (b - k)) :=
        Nat.mul_le_mul_left _ hfactor
      _ = b * ((b + 1) ^ k * (b - k)) := by ring
      _ ≤ b * b ^ (k + 1) := Nat.mul_le_mul_left b hprev
      _ = b ^ (k + 1 + 1) := by ring

/-- The next kth power is at most twice the current one once b≥2k. -/
theorem next_power_le_twice {k b : ℕ} (hb : 0 < b) (hk : 2 * k ≤ b) :
    (b + 1) ^ k ≤ 2 * b ^ k := by
  have hprev := succ_pow_mul_sub_le k b (by omega)
  have hfactor : b ≤ 2 * (b - k) := by omega
  have hmul := Nat.mul_le_mul_left ((b + 1) ^ k) hfactor
  have hbound : (b + 1) ^ k * b ≤ (2 * b ^ k) * b := by
    rw [pow_succ] at hprev
    nlinarith
  by_contra h
  have hstrict := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge h) hb
  exact (Nat.not_lt_of_ge hbound) hstrict

/-- Length after adjoining the next n distinct positive kth powers. -/
def tailLength (k B L n : ℕ) : ℕ :=
  L + ∑ i ∈ Finset.range n, (B + i + 1) ^ k

theorem tailLength_zero (k B L : ℕ) : tailLength k B L 0 = L := by
  simp [tailLength]

theorem tailLength_succ (k B L n : ℕ) :
    tailLength k B L (n + 1) = tailLength k B L n + (B + n + 1) ^ k := by
  simp [tailLength, Finset.sum_range_succ, Nat.add_assoc]

/-- The interval-length invariant persists through every finite tail extension. -/
theorem tailInterval_invariant {k B a L : ℕ}
    (hI : representedInterval k B a L)
    (hL : (B + 1) ^ k ≤ L) (hB : 2 * k ≤ B + 1) (n : ℕ) :
    representedInterval k (B + n) a (tailLength k B L n) ∧
      (B + n + 1) ^ k ≤ tailLength k B L n ∧ n ≤ tailLength k B L n := by
  induction n with
  | zero =>
    simpa only [Nat.add_zero, tailLength_zero] using
      And.intro hI (And.intro hL (Nat.zero_le L))
  | succ n ih =>
    obtain ⟨hIn, hLn, hnn⟩ := ih
    have hcoin : 0 < (B + n + 1) ^ k := pow_pos (by omega) k
    have hnext : (B + n + 1 + 1) ^ k ≤ 2 * (B + n + 1) ^ k :=
      next_power_le_twice (by omega) (by omega)
    have hInext := representedInterval_add_next hIn (hLn.trans (Nat.le_succ _))
    rw [tailLength_succ]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Nat.add_assoc] using hInext
    · have hsum : 2 * (B + n + 1) ^ k ≤
          tailLength k B L n + (B + n + 1) ^ k := by omega
      simpa only [Nat.add_assoc] using hnext.trans hsum
    · omega

/-- A sufficiently long represented interval gives all sufficiently large sums.
The proof adjoins only previously unused bases, so distinctness is preserved. -/
theorem threshold_of_representedInterval {k B a L : ℕ} (hk : 0 < k)
    (hI : representedInterval k B a L)
    (hL : (B + 1) ^ k ≤ L) (hB : 2 * k ≤ B + 1) :
    a ∈ thresholds (kthPowers k) := by
  intro m hma
  obtain ⟨hIm, _, hmL⟩ := tailInterval_invariant hI hL hB m
  have hrep : representedUpTo k (B + m) m :=
    hIm m hma (by omega)
  exact (represented_iff_mem_subsetSums hk).mp (representedUpTo_represented hrep)

theorem exists_least_threshold_of_threshold {A : Set ℕ} {a : ℕ}
    (ha : a ∈ thresholds A) : ∃ b : ℕ, IsLeast (thresholds A) b := by
  classical
  have hex : ∃ b : ℕ, b ∈ thresholds A := ⟨a, ha⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hb => Nat.find_min' hex hb⟩

theorem exists_least_threshold_of_representedInterval {k B a L : ℕ} (hk : 0 < k)
    (hI : representedInterval k B a L)
    (hL : (B + 1) ^ k ≤ L) (hB : 2 * k ≤ B + 1) :
    ∃ b : ℕ, IsLeast (thresholds (kthPowers k)) b :=
  exists_least_threshold_of_threshold (threshold_of_representedInterval hk hI hL hB)

end Erdos345
