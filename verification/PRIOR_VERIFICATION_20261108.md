# Dated verification record

**Formal target: PASS at the checked source revision. Packaged source identity:
PASS. No new execution is inferred from repackaging.**

The source build and external checks described below were actually completed for
development commit `75737122fb44f5f53981b502f05988165f12cac7` and recorded at
`2026-11-08T10:09:28.495530+00:00`. On `2026-11-10T06:12:00.433289+00:00`, all 357 packaged
Lean sources were independently rehashed against the successful source manifest
and the Git objects of that revision. All matched byte for byte. The pinned
toolchain, Lake project definition and dependency lockfile also match.

The release is a clean repository snapshot rather than a publication of the
private development history. Its commit identity is different. Packaging changes
concern documentation, `.gitignore` and byte-preserving `.gitattributes`, not
mathematical source or the toolchain. The report does **not** claim that the new
release commit has undergone a second clean build or a second kernel replay.

The integrity review also rehashed **1,075** retained evidence files,
**39,347,216 bytes**, against their recorded manifest. All matched. Full raw logs
and machine-specific receipts remain in the private archive; this portable
summary does not publish their private paths.

| Check | Actual result |
| --- | --- |
| Isolated fresh project-source compilation | 357/357 source modules passed; no prebuilt project proof objects copied |
| Full axiom audit | 1,497 registered constants checked |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Original-statement comparison | Passed; no definition holes allowed |
| Lean default kernel | Passed in the statement comparator |
| Additional proof checkers | Lean paranoid, Lean4Lean, Nanoda, con-leche and con-ron passed |
| Original-problem coverage | Positive bases, distinct sums, least thresholds, adjacent strict comparison, infinitely many positive indices |

All external stages used the same immutable solution export:

| Stage | Outcome | Recorded seconds |
| --- | --- | --- |
| challenge_compile | PASS, exit 0 | 4.530 |
| challenge_export | PASS, exit 0 | 5.583 |
| target_audit | PASS, exit 0 | 13.300 |
| solution_export | PASS, exit 0 | 109.824 |
| statement_comparator | PASS, exit 0 | 222.857 |
| lean_paranoid | PASS, exit 0 | 233.716 |
| lean4lean | PASS, exit 0 | 224.856 |
| nanoda | PASS, exit 0 | 115.108 |
| con_leche | PASS, exit 0 | 239.669 |
| con_ron | PASS, exit 0 | 200.462 |

Solution export SHA-256:
`915c6be8e401103abd7281f8262334b5a9c8ffe09cd19ad25624cc889ad96da7`.

Challenge export SHA-256:
`9b05b706cd6defdf2932cb7eefbe0a8c892e1a3b2cc3c149f491b71a7343f8df`.

The actual build used Lean 4.35.0-rc3 (Lean source revision
`470d5ce1400764999581fd26d5d72b00d990b0f4`) and the Mathlib revision in the
lockfile. Dependency caches, their source identities, and the native toolchain
remain part of the execution trust. Multiple proof checkers strengthen the
mechanical evidence; they do not certify the paper's every intermediate argument,
historical novelty, author identity, sponsor acceptance or prize entitlement.

This was assistant-led verification, not an independent human referee report.
The paper was also reread and all 14 rendered pages inspected during preparation.
Its references were checked against the available primary sources. The PDF was rebuilt after correcting Shiu's article-title spelling from
"Titschmarsh" to "Titchmarsh"; the mathematical text is unchanged. All 14 final
page renders were inspected, and pages 1–13 are pixel-identical to the prior PDF.

The scope matrix is in [STATEMENT.md](../STATEMENT.md), reproduction commands in
[REPRODUCTION.md](../REPRODUCTION.md), exact source hashes in
[source-identity.json](source-identity.json), and the portable execution summary
in [check-summary.json](check-summary.json). These facts support a submission for
review, not a claim that the sponsor has already approved the result.
