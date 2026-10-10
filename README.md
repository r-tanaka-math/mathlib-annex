# MathlibAnnex

MathlibAnnex is a project-independent, Mathlib-first library of reusable Lean declarations.
**v0.5.0 is a source-only Geometric Structure Spaces (GSS) release.** It adds 328 GSS
library modules and an imports-only Project entry, while retaining the v0.4.0 library
and its five Project entries. The complete library contains 732 modules and six
Project facades; the root is `MathlibAnnex` and the Lake package is `mathlibAnnex`.

```lean
import MathlibAnnex.Projects.GeometricStructureSpaces
```

The GSS facade has 13 direct roots and resolves to 309 GSS modules plus 57 existing
Annex providers. `import MathlibAnnex` covers all 328 GSS modules, including the
19 outside that facade closure. Facades contain comments and imports only; they
introduce no declarations, aliases, instances or copied proofs.

The six Project source entries are:

| Project | Import | Source manifest |
| --- | --- | --- |
| Geometric Structure Spaces | `MathlibAnnex.Projects.GeometricStructureSpaces` | [GSS](docs/projects/geometric-structure-spaces.json) |
| Mankiewicz | `MathlibAnnex.Projects.Mankiewicz` | [Mankiewicz](docs/projects/mankiewicz.json) |
| Sphere Rigidity | `MathlibAnnex.Projects.SphereRigidity` | [Sphere Rigidity](docs/projects/sphere-rigidity.json) |
| Rosenberg | `MathlibAnnex.Projects.Rosenberg` | [Rosenberg](docs/projects/rosenberg.json) |
| Naimark | `MathlibAnnex.Projects.Naimark` | [Naimark](docs/projects/naimark.json) |
| Pure State Homogeneity | `MathlibAnnex.Projects.PureStateHomogeneity` | [Pure State Homogeneity](docs/projects/pure-state-homogeneity.json) |

## Qualified source and environment

Hosted run **38063627833, attempt 1** passed all 14 required gates for commit
`4d4cfc1b2b5a2642a6a90d3fc5c4e6f4f8abdfa4`, tree
`2df11956be5a3b1c55827c291d74bfc03cd6727c`. The 739 targets comprise 312 verified
checkpoint restorations and 427 fresh native Linux compilations. The final
module-origin audit covers 14,281 declarations, including 6,029 GSS declarations,
and matches all 3,252 public GSS names. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed axioms.

- Lean: `leanprover/lean4:v4.32.0-rc1`.
- Mathlib: `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
- All nine dependencies: exact committed [lake-manifest.json](lake-manifest.json).

This public projection preserves all 756 Lean files, dependency pins, executable
workflow/helpers, module keys and proof evidence from that qualified source.
Only release documentation and metadata differ. The [v0.5.0 release](docs/releases/v0.5.0.md)
and [verification record](VERIFICATION.md) explain the external binding to the
actual public commit, tree, annotated tag and asset hashes.

Qualification is checkpoint-assisted with normal Lean kernel acceptance and a
final compiled-axiom audit. Independent single-runner clean qualification is
`NOT_RUN`; the whole of Mathlib was not rebuilt without caches. This release
does not certify full-paper semantic correspondence, novelty, LFH Cards or
website publication. Previous tags and historical records are retained.

## License and corrections

Original Lean source, facades, examples, repository software and ordinary technical
documentation use the [Apache License 2.0](LICENSE). External components retain
their terms; see [Third-party notices](THIRD_PARTY_NOTICES.md). This license does
not cover separately published LFH content, research documents, website editorial
content or private Workbench/LFH technology. No dependency cache or toolchain is
vendored. This AI-assisted source is selected and maintained by Ryotaro Tanaka;
no novelty or first-formalization claim is made. See [Contributing](CONTRIBUTING.md)
for corrections against exact revisions and [the historical naming migration](docs/naming-migration-v0.4.0.md)
for changes introduced before this release.
