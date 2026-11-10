# Correspondence with Erdős problem 345

Original source: [Erdős problem 345](https://www.erdosproblems.com/345), with the
historical formulation in Erdős and Graham, *Old and New Problems and Results
in Combinatorial Number Theory* (1980), printed p. 55. The JSP mapping is
**JSP-000287**. The proposed formal statement requires the sponsor's review;
maintainer approval of this statement is not claimed.

The definitions appear in `Erdos345/Statement.lean`:

```lean
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ A ∧ n = ∑ b ∈ B, b}

def kthPowers (k : ℕ) : Set ℕ :=
  {x | ∃ n : ℕ, 0 < n ∧ n ^ k = x}

def thresholds (A : Set ℕ) : Set ℕ :=
  {m | ∀ n : ℕ, m ≤ n → n ∈ subsetSums A}

def IntendedStatement : Prop :=
  {k : ℕ | 0 < k ∧ ∃ a b : ℕ,
    IsLeast (thresholds (kthPowers k)) a ∧
    IsLeast (thresholds (kthPowers (k + 1))) b ∧ b < a}.Infinite
```

| Original requirement | Formal realization |
| --- | --- |
| Positive integer bases | `0 < n` in `kthPowers` |
| Finite sums of distinct powers | A `Finset` of power values contained in `kthPowers k`; for positive k, exponentiation on positive bases is injective |
| Every sufficiently large integer | Universal quantifier over all `n ≥ m` in `thresholds` |
| The actual least threshold | `IsLeast`, for both exponents; existence for every positive exponent is proved separately |
| Adjacent exponents | `k` and `k + 1` |
| Strict decrease | `b < a` |
| Infinitely many positive indices | `Set.Infinite` together with `0 < k` |
| Unconditional conclusion | `Erdos345.erdos_345 : IntendedStatement`, with no theorem hypotheses |

The convention is the least inclusive threshold. Using the last exceptional
integer instead subtracts one from both thresholds for k at least two and
preserves strict comparisons. Allowing the empty sum affects zero only. The
degree-one boundary can affect only finitely many indices. These conventions
therefore preserve the asserted infinitude.

The independent statement comparator used a separately reconstructed specification
with **no permitted definition holes**. Its admitted target was only the requested
type in a separate checking environment and was never imported by the solution.
The recursive comparison and production-axiom audit passed. Source comments
describing intermediate obligations as pending are retained historical comments;
the final theorem supplies those obligations by proved declarations.
