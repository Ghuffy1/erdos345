# Reproduction

Use a fresh checkout of the exact release commit named in the submission, with
Elan/Git and the pinned toolchain available. Run from the repository root:

```text
lake exe cache get
lake build
lake env lean -j 1 -M 6144 -DautoImplicit=false Audit.lean
```

`lean-toolchain` pins `leanprover/lean4:v4.35.0-rc3`. `lakefile.toml` pins Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`; `lake-manifest.json` fixes all nine
dependency revisions. Do not run `lake update` or substitute a different profile.

The first command obtains dependency caches. The second must build this project's
proof objects from source: this release contains no `.lake` directory, compiled
proof objects or dependency cache. `Erdos345.lean` imports the complete local proof
library; the separate `Audit.lean` checks all 1,497 registered constants, including
`Erdos345.erdos_345`. Resource requirements can be substantial. The fresh verification recorded
in [the report](verification/REPORT.md) used native Windows: initially sequential
compilation, then two independent source workers with one Lean thread and a
6 GiB allocation limit per worker. It used controlled import paths and separate
source/output directories, without an operating-system sandbox. No measured
peak physical-RAM claim is made.

The target theorem is in `Erdos345/Conclusion.lean` and has type
`Erdos345.IntendedStatement`. Its recorded axiom output is:

```text
'Erdos345.erdos_345' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the only axioms reported for every audited declaration. No admitted
challenge theorem is imported by the production proof. The statement audit is
described in [STATEMENT.md](STATEMENT.md) and the dated execution record in
[verification/REPORT.md](verification/REPORT.md).

These commands describe reproduction from the selected source commit. The
verification report records the separate commands that were actually executed
and binds their results to that commit; this documentation revision is later.
