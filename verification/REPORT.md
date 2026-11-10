# Fresh verification of Erdős 345

**Verdict: Verification passed for proof commit `78012848fd02d20ffd2d2dec70fdc7408483f201`.** The checked formal
development proves the full infinitude assertion of Erdős problem 345, with no
extra mathematical hypothesis beyond the standard classical Lean foundations.
The corresponding JSP entry is **JSP-000287**.

This fresh execution was recorded at **2026-11-10T19:25:38.337502+00:00**. It rebuilt
all 357 project source modules in a new output directory, checked all 1,497
registered constants, compared an independently defined original-problem
specification with no definition holes, and passed all six kernel-checking
routes. No project proof object from the earlier verification was reused.

| Required judgment | Conclusion | Evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes | Positive bases, finite distinct sums, actual least thresholds, adjacent exponents, strict decrease, and infinitely many positive indices |
| Did the specified commit actually pass? | Yes | A fresh source build in separate directories, full axiom audit, statement comparator and all external stages |
| Does it fully solve the original problem? | Yes, within the stated formal trust | `Erdos345.erdos_345 : Erdos345.IntendedStatement` is a closed theorem |
| Does it meet the Lean completeness requirements? | Meets | Complete scope, no admitted production proof, no added unproved assumption |

The source is fixed at the full commit above. This report is deliberately stored
in a later documentation commit; that does not change the selected proof commit
or claim a compiler execution of the later documentation revision. The source
manifest binds every checked Lean file to its actual bytes.

## Execution and trust

The run used Lean **4.35.0-rc3**, source revision
`470d5ce1400764999581fd26d5d72b00d990b0f4`, and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. All nine dependency source revisions
were freshly checked against the lockfile with clean tracked source trees.
The 23,904 dependency-cache parts were covered by the recorded hash checks.
Dependency caches are an explicit input; project outputs were newly generated.

The completed run used native Windows, separate source and output directories,
and controlled import paths. It did not use an operating-system sandbox.
Compilation began sequentially and continued with two independent source workers,
each using `-j 1` and Lean's 6 GiB allocation limit. A module was scheduled only
after its local imports had completed. The interruption and unreceipted output
were retained privately; only successful, hash-verified records count.
All dependency-copy hashes were checked after the proof checks, and all
project-object hashes and tool executable hashes were rechecked. The only
project objects used were newly compiled from the selected source commit.

A preliminary Linux run recorded 320 successful modules before its host service
stopped. Read-only recovery found 37 object checksum mismatches. Every Linux
output was excluded from this completed Windows run. Earlier setup, timeout and
recovery records remain private; none is counted as a successful final check.
All 9,378 recorded standard-toolchain input parts were also rehashed. No peak
physical-memory measurement is claimed.

The comparator used its documented `--inadvisably-no-sandbox` option with both
`--challenge-from-export` and `--solution-from-export`. Its warning was:
`WARNING: Sandbox disabled, this run is not trustworthy.`
In this mode it reads the already generated, hash-bound exports;
it does not load the project configuration or build the project again. The
statement comparison, permitted-axiom check and kernel replay remain enabled.
No operating-system isolation is claimed; the host and checker executables
remain trust inputs.


The only audited axioms are **`propext`, `Classical.choice`, and `Quot.sound`**.
No `sorryAx` or additional assumption is present in the audited proof. The
stronger unused Fan–Pollack interface is not an assumption of the final theorem.

| Stage | Actual result | Seconds |
| --- | --- | --- |
| challenge_compile | PASS (exit 0) | 6.078 |
| challenge_export | PASS (exit 0) | 5.766 |
| target_audit | PASS (exit 0) | 13.531 |
| solution_export | PASS (exit 0) | 73.156 |
| statement_comparator | PASS (exit 0) | 172.344 |
| lean_default | PASS (exit 0) | 149.562 |
| lean_paranoid | PASS (exit 0) | 174.235 |
| lean4lean | PASS (exit 0) | 202.296 |
| nanoda | PASS (exit 0) | 97.125 |
| con_leche | PASS (exit 0) | 231.704 |
| con_ron | PASS (exit 0) | 191.625 |

The successful statement comparator also ran Lean's default kernel on the
solution export. The other routes were Lean paranoid, Lean4Lean, Nanoda,
con-leche and con-ron. Every route checked the same immutable solution export.

Solution export SHA-256:
`915c6be8e401103abd7281f8262334b5a9c8ffe09cd19ad25624cc889ad96da7`.

Challenge export SHA-256:
`9b05b706cd6defdf2932cb7eefbe0a8c892e1a3b2cc3c149f491b71a7343f8df`.

The independent challenge reconstructs the original definitions without
importing the submitted proof. Its admitted target describes only the requested
type in a separate environment; it is never imported by production code.
The comparator permits no definition holes, and the solution must replace that
target with a proof using only the three permitted foundational axioms.

## Mathematical and documentary scope

The [statement correspondence](../STATEMENT.md) covers every original requirement.
The original printed formulation in Erdős and Graham (1980), p. 55, was reread.
The inclusive-threshold and degree-one conventions do not change the infinitude
claim. [Reproduction instructions](../REPRODUCTION.md) identify the ordinary
project commands; the actual verification here used the per-module
source build described above.

The 14-page paper was freshly rendered and visually reviewed. Its SHA-256 is
`fa8e150cedfd7a11dd9b1b70d1a8cd1aee02c124f9f33fceaf97a4633c6ab72f`. No further change was required. Its main result is
Theorem 1.1 on p. 1, with the concluding proof on p. 14. The paper and formalization
use some different intermediate arguments, as documented in
[PAPER_AND_FORMALIZATION.md](../PAPER_AND_FORMALIZATION.md); the kernel checks are
not a line-by-line certification of the PDF.

This is assistant-led verification using independent proof-checking programs,
not an independent human referee report or sponsor approval. The result does not
certify historical priority, author identity, prize eligibility or entitlement.
The unavailable 2019 Haenel–Wood poster remains disclosed in
[PRIOR_WORK.md](../PRIOR_WORK.md). Raw machine-specific logs remain private.

Portable evidence: [check summary](check-summary.json),
[fresh source manifest](fresh-source-manifest.json), and
[complete axiom audit](axiom-audit.json). The earlier verification is retained as
[a historical record](PRIOR_VERIFICATION_20261108.md).
