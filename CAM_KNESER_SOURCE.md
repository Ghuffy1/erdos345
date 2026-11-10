# Kneser dependency provenance and migration

Kneser's addition theorem is a pre-existing mathematical and Lean result. It is a dependency of Lev's interval argument, not a claim of a new result in this project.

Authors of the imported development: Mantas Bakšys and Yaël Dillies. Their copyright and Apache 2.0 notices are retained in the source headers. The license is copied to CAM_KNESER_LICENSE.

The initial archived source was YaelDillies/cam-combi at revision 58efa34adc943ba7f55f9ae9a423215dafccf52a. Its Kneser.lean and MulStab.lean contain no proof placeholders. The separate KneserRuzsa.lean contains an unfinished proof and is excluded from the compiled development. Frozen reference copies are under sources/cam_combi_58efa34/.

The path history explains that the maintained code moved to MiscYD, now named [YaelDillies/misc-yd](https://github.com/YaelDillies/misc-yd). The final source chosen for migration is revision f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba:

- MiscYD/AddCombi/Kneser/Kneser.lean, Git blob 4fcd566e4b2f80c99d5b9b5a357b39904080d5c2.
- MiscYD/AddCombi/Kneser/MulStab.lean, Git blob 2525e2b18864f3071ae09502acbd07903fad5005.

The maintained source targets Lean 4.36.0-rc2. The local migration keeps the existing Erdős project on Lean 4.35.0-rc3 and mathlib c55e6e786f49471c72fbddbec5415808896aec1e. Module/export directives are adapted to the existing project, imports point to the local checked module, and the strong-induction case name is adapted to the pinned version. Further changes, if needed, are visible in the local source diff. Shared dependencies are not modified.

The imported public names remain in their original Finset namespace. Their automatically generated additive theorems must be included in the axiom audit, as well as the handwritten multiplicative source. verification/CamKneserInventory.lean obtains the public theorem inventory from the actual compiled module metadata. An inventory or a successful dependency migration alone does not prove the original Erdős problem.

The final imported inventory contains 173 public theorem constants, including generated helpers and one generated Set helper. All are included in the source-matched axiom audit, which reports only propext, Classical.choice and Quot.sound. The original maintained source hashes are 7173cd8f1bc92bb620391655fa5619481fec425ad29034f26fd69a3b96bec030 and 8f6872914a8830fb89b8ff39fc609ef79cb16221ba4f45cc0ac0c6fee4bc7608; their Git blob hashes independently match the two published blobs above. The current source license matches the archived license byte for byte.

The earlier migration attempts and compiler failures are preserved in sources/ and verification/. No failed compile is represented as a successful proof. The ultimate verification outcome is recorded by the current source-matched receipts and audit, not by this provenance note.

No source author was contacted. Nothing was submitted or published.
