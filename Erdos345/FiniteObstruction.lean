import Erdos345.Representations
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.BigOperators

namespace Erdos345

/-- The maximum sum of a subset of the bases from zero through H. -/
def baseSum (H : ℕ) : ℕ := ∑ n ∈ Finset.range (H + 1), n

/-- The residue obstruction concerns the actual integer m, not just a residue. -/
theorem not_represented_of_residue {k H Q m : ℕ}
    (hbelow : m < (H + 1) ^ k)
    (hphase : ∀ n : ℕ, n ≤ H → n ^ k % Q = n % Q)
    (hresidue : baseSum H < m % Q) : ¬ represented k m := by
  rintro ⟨B, _, hsum⟩
  have hB : ∀ b ∈ B, b ≤ H := representation_bases_le hbelow hsum
  have hsubset : B ⊆ Finset.range (H + 1) := by
    intro b hb
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hB b hb))
  have hmod : m % Q = (∑ b ∈ B, b) % Q := by
    calc
      m % Q = (∑ b ∈ B, b ^ k) % Q := congrArg (fun a => a % Q) hsum.symm
      _ = (∑ b ∈ B, b ^ k % Q) % Q := Finset.sum_nat_mod B Q (fun b => b ^ k)
      _ = (∑ b ∈ B, b % Q) % Q := by
        congr 1
        exact Finset.sum_congr rfl (fun b hb => hphase b (hB b hb))
      _ = (∑ b ∈ B, b) % Q := (Finset.sum_nat_mod B Q id).symm
  have hle : m % Q ≤ baseSum H := by
    rw [hmod]
    exact (Nat.mod_le _ _).trans (Finset.sum_le_sum_of_subset hsubset)
  exact (Nat.not_lt_of_ge hle) hresidue

/-- Fermat's congruence includes bases divisible by the prime. -/
theorem shifted_power_mod_prime {p t : ℕ} (hp : p.Prime) (hd : p - 1 ∣ t)
    (n : ℕ) : n ^ (t + 1) % p = n % p := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.natCast_eq_natCast_iff' (n ^ (t + 1)) n p).mp
  simp only [Nat.cast_pow]
  by_cases hn : (n : ZMod p) = 0
  · simp [hn]
  · obtain ⟨d, rfl⟩ := hd
    have hunit : (n : ZMod p) ^ (p - 1) = 1 := by
      have hu := pow_card_eq_one (x := Units.mk0 (n : ZMod p) hn)
      have hval := congrArg Units.val hu
      simpa [Fintype.card_units] using hval
    rw [pow_succ, pow_mul, hunit, one_pow, one_mul]

/-- The congruence holds for the product of any finite set of eligible primes. -/
theorem shifted_power_mod_prime_product (P : Finset ℕ) (t n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p - 1 ∣ t) :
    n ^ (t + 1) % (∏ p ∈ P, p) = n % (∏ p ∈ P, p) := by
  classical
  revert hP hdiv
  induction P using Finset.induction_on with
  | empty => intro _ _; simp only [Finset.prod_empty, Nat.mod_one]
  | @insert p P hp ih =>
    intro hP hdiv
    have hprime : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hdiv' : ∀ q ∈ P, q - 1 ∣ t := fun q hq => hdiv q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hprime (hP' q hq)).mpr
      intro heq
      exact hp (heq ▸ hq)
    rw [Finset.prod_insert hp]
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
    exact ⟨shifted_power_mod_prime hprime (hdiv p (Finset.mem_insert_self p P)) n,
      ih hP' hdiv'⟩

/-- Every residue occurs among the last Q integers below A. -/
theorem residue_in_top_interval {A Q r : ℕ}
    (hQ : 0 < Q) (hQA : Q ≤ A) (hr : r < Q) :
    ∃ m : ℕ, A - Q ≤ m ∧ m < A ∧ m % Q = r := by
  let d := (A - 1 - r) / Q
  let m := Q * d + r
  have hdecomp := Nat.mod_add_div (A - 1 - r) Q
  have hrem := Nat.mod_lt (A - 1 - r) hQ
  have hrA : r ≤ A - 1 := by omega
  have hm : m + (A - 1 - r) % Q = A - 1 := by
    dsimp [m, d]
    omega
  refine ⟨m, ?_, ?_, ?_⟩
  · omega
  · omega
  · dsimp [m]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- Produce a genuine exceptional integer from a uniform residue obstruction. -/
theorem exists_exception_from_residue {k H Q : ℕ}
    (hQ : 0 < Q) (hQA : Q ≤ (H + 1) ^ k)
    (hgap : baseSum H + 1 < Q)
    (hphase : ∀ n : ℕ, n ^ k % Q = n % Q) :
    ∃ m : ℕ, (H + 1) ^ k - Q ≤ m ∧ m < (H + 1) ^ k ∧
      ¬ represented k m := by
  obtain ⟨m, hlo, hhi, hmod⟩ :=
    residue_in_top_interval hQ hQA hgap
  refine ⟨m, hlo, hhi, not_represented_of_residue hhi (fun n _ => hphase n) ?_⟩
  rw [hmod]
  exact Nat.lt_succ_self (baseSum H)

end Erdos345
