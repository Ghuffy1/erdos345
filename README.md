# Erdős 345: infinitely many decreases of distinct-power thresholds

**Theorem.** If T(k) is the least inclusive threshold above which every integer
is a sum of distinct positive k-th powers, then T(k+1) < T(k) for infinitely
many positive integers k.

Authors: Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer, in alphabetical order by surname. The authors report equal
contributions to the mathematical solution and its Lean formalization.

The corresponding Justin Sun Prize catalogue entry is **JSP-000287**.

- [Mathematical paper](paper/erdos345-proof.pdf), Theorem 1.1, with the concluding proof on p. 14.
- [Paper source](paper/erdos345-proof.tex).
- [Formal statement](Erdos345/Statement.lean): `Erdos345.IntendedStatement`.
- [Concluding theorem](Erdos345/Conclusion.lean): `Erdos345.erdos_345`.
- [Reproduction](REPRODUCTION.md), [statement correspondence](STATEMENT.md), and
  [verification record](verification/REPORT.md).
- [Authorship and AI assistance](AUTHORS.md), [third-party attribution](THIRD_PARTY.md),
  and [relationship between the paper and formalization](PAPER_AND_FORMALIZATION.md).

The 357 Lean source files are byte-identical to those checked at development
revision `75737122fb44f5f53981b502f05988165f12cac7`. This release is a clean source snapshot with revised packaging
and documentation; its Git revision is separate from that development revision.
The report identifies the actual execution date and the source-equivalence check.
No claim is made that packaging creates a new compiler execution.

Lean is pinned to **4.35.0-rc3**, and Mathlib to
`c55e6e786f49471c72fbddbec5415808896aec1e`. The Conjectures.io single-file profile
uses a different toolchain and is not part of this project.

This is a privately prepared submission source tree. Neither its preparation
nor its local verification establishes publication, independent human review,
world priority, JSP acceptance, eligibility, or an award.
