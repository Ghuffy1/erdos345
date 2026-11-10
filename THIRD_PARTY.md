# Third-party mathematical and formal sources

The paper's bibliography credits its mathematical inputs. The formalization also
uses the following pre-existing libraries and developments.

| Source | Pinned revision / attribution | Local material |
| --- | --- | --- |
| Lean and Mathlib | Lean 4.35.0-rc3; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, with transitive revisions fixed by `lake-manifest.json` | Dependency references, not vendored Mathlib |
| Kneser's addition theorem formalization | Mantas Bakšys and Yaël Dillies; [misc-yd](https://github.com/YaelDillies/misc-yd/tree/f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba), revision `f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba` | Local compatible modules with original notices; [Apache 2.0 license](CAM_KNESER_LICENSE) |
| Prime-distribution formalization | [OpenAI mathematics repository](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/PrimeGaps), revision `4eaee87548250b2682affda7d05d947c05554bae` | 48 local compatibility modules under `OAI/NumberTheory/PrimeGaps/`; [Apache 2.0 license](OAI/LICENSE) |

The Kneser migration adapts imports, module/export directives and an induction
case name to this project's pinned versions. The prime-distribution migration
uses explicit imports and compatible arithmetic proofs; its theorem statements
are unchanged. The final local sources, rather than an assertion about unchanged
upstream compilation, are covered by the source manifest and verification.

The original [Kneser provenance note](CAM_KNESER_SOURCE.md) and
[prime-distribution provenance note](OAI_SOURCE.md) are retained verbatim as
historical records. References in those notes to development snapshots, failed
attempts, and internal diagnostic directories describe the private development
archive, which is not included in this clean source tree.

No ownership or novelty is claimed for these pre-existing results. Their licenses
and source notices must be retained in any later distribution.
