# Third-party sources and retained terms

The retained Apache-2.0 license text is `LICENSES/Apache-2.0.txt`.
Exact public commits, Git blob identities, source SHA-256 values, actual-read
spans and frozen-source origins are recorded in `PROVENANCE.json` and its
review records. Per-declaration API reuse and proof adaptation are separated
in `REUSE_LEDGER.json`.

The Mathlib project is used at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its original file-specific
copyright and author notices remain with the upstream files; this package
does not redistribute their complete sources or claim authorship of them.

The pinned Annex and accepted provider contributions retain this notice:

Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka

This handoff uses the current dispatch's observed public Annex commit
`c05416f17362be14582ab1bce7d70b41aab6dffc` and retains the earlier baseline
`5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e` as lineage. The supplied A W03,
B W03 and C W02 sources remain frozen source candidates owned by their
existing writers. Their license/attribution status is not upgraded here.

Specific adaptations in the new sources:

- `CompressionCorner`: closed convergence-locus argument adapted from the
  existing B `Enveloping/ApproximateUnit` route, using the existing envelope,
  corner and central-support objects.
- `Sakai`: non-type-I generalization of B W03 `Enveloping/FactorRestriction`,
  preserving actual restriction and surjective quotient diagrams.
- `UnitizationSubquotient`: the actual unitization-range construction in
  A W03 `TypeI/NonUnitalGCRSubalgebra` is extracted and extended with the
  displayed quotient diagram. Mathlib's maps/equivalence and Annex's closed
  range theorem are reused unchanged.
- The other new mathematical proofs compose the individually cited APIs
  and implement the dispatch's mathematical minimal-column proposal.
  `IsAbelianProjection` from a minimal projection is reused from frozen C
  `TypeI/FiniteDimensional`, not redeclared in this handoff.

The static scanner and safe ZIP helper are unchanged dispatch utilities.
The lexical source-inventory helper adapts the same B writer's W01 metadata
utility and adds `attribute`, `include` and `omit` context recording. None is
a Lean parser, elaborator or kernel checker.

New W04 contributions are source candidates intended for Apache-2.0,
subject to the owner's exact release decision. This private source handoff
does not infer a release grant, publish the contribution, or assert kernel
validation. The current task performs no remote publication.
# W05 continuation notice

The W04 notices below are retained. W05 adds actual finite-stage CAR trace
compressions, their common pointwise-WOT cluster map, and unconditional
classification assembly. Mathlib's matrix/operator equivalences, adjoint
positivity, positive-map continuity and cluster-point APIs are used on their
existing carriers. The existing Annex CAR model and fixed accepted-source
providers are reused, without copying their full source into this Return.

The elementary nonzero-range-vector normalization adapts the same B writer's
W04 MinimalColumn proof. The closed-family cluster route references the fixed
B CommutantRetraction proof, and the reverse-Sakai assembly adapts the W04
conditional typed consumer with its concrete map input discharged. Exact
source identities, spans and declaration-level decisions are in PROVENANCE
and REUSE_LEDGER. Original copyright/license terms remain in force. New work
is intended for Apache-2.0; no exact publication grant or release is asserted.

