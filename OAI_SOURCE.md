# OAI prime-distribution dependency

The `OAI/NumberTheory/PrimeGaps/` sources are local compatibility copies from [openai/math at 4eaee87548250b2682affda7d05d947c05554bae](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/PrimeGaps), released under Apache-2.0. Their mathematical authorship is attributed to that source, not to this project's new counting argument.

`OAI/LICENSE` and `sources/oai_prime_distribution_20261108/LICENSE` preserve the license. The latter directory contains immutable original bytes under `raw/`, expected Git blob identities, local source hashes and a generated patch showing local changes. An uncompiled file is not counted as a verified theorem.

The compatibility work replaces the original umbrella import with explicit imports, adding further imports needed by this project's pinned library. The original toolchain was Lean 4.34.1; this project uses Lean 4.35.0-rc3. Compiler receipts record exactly which local files passed. The upstream general build configuration is saved as text and is not used to install unrelated dependencies.

The local `ConductorBounds` copy also uses explicit multiplication and addition bounds and narrower arithmetic-tactic inputs. Its theorem statements are unchanged. The original source and each local change remain distinguishable in the saved patch. Imported files that exceed the default 2 GiB Lean limit are retried explicitly at 4 GiB; actual limits and failed attempts are retained in their receipts.

All 48 modules now compile locally and belong to the closed proof's source closure. The Siegel--Walfisz and Bombieri--Vinogradov declarations are explicitly included in the full development axiom audit. Isolated reproduction and independent checker results remain a separate stage. See `PROGRESS_CLOSED_TARGET.md`, `verification/oai_development/` and `sources/oai_prime_distribution_20261108/LOCAL_SOURCE_INVENTORY.json`.
