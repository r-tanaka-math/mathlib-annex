# MathlibAnnex

MathlibAnnex is a project-independent, Mathlib-first library of reusable Lean declarations. The 0.3.0 private release candidate includes Project import entries for the Mankiewicz Extension Theorem, Sphere Rigidity, and Rosenberg formalizations. The intended source tag is `v0.3.0`; publication has not occurred. The Lake package is `mathlibAnnex`; its root import is `MathlibAnnex`.

## Mankiewicz source entry

The mathematical scope covers affine-isometry extension on open connected domains, an ambient-interior convex-set corollary, and positive-radius ball corollaries over real normed spaces. Finite dimensionality and completeness are not added. The whole-space Mazur–Ulam theorem remains provided by Mathlib.

```lean
import MathlibAnnex.Projects.Mankiewicz
#check MathlibAnnex.IsometryEquiv.existsUnique_affineExtension
```

The Project entry contains only comments and imports. It introduces no declaration, instance, notation, alias or copied proof. Canonical declarations remain in mathematically organized modules. The root `MathlibAnnex` import remains available. [Root import example](examples/Import.lean) and [Project import example](examples/ImportMankiewicz.lean) demonstrate both entry points.

The [Project Source Manifest](docs/projects/mankiewicz.json) records entry bytes, direct roots, the resolved MathlibAnnex source closure, dependency identities and compiled-axiom policy. It binds source content without referring to the Git commit or tree that contains the manifest. Actual immutable release identities and the exact successful qualification receipt belong to the external publication record described in [Verification](VERIFICATION.md).

## Rosenberg source entry

The candidate adds 60 reusable modules for the Rosenberg theorem route. The source admits genuinely non-unital complex C*-algebras and retains the exact separability, nonzero irreducibility, singleton-equivalence-class, compact-image, and compact-preimage conclusions established by the Lean declarations. The Project facade is navigation only; reusable ownership remains in the library modules.

```lean
import MathlibAnnex.Projects.Rosenberg
#check MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation.isCompactOperatorModel_of_singleton
```

The [Rosenberg Project Source Manifest](docs/projects/rosenberg.json) binds the two direct roots, exact 60-module closure and import edges, entry bytes, environment pins, parser qualification contract, and external publication boundary. It does not publish Cards or a Project view.

## Reproducible environment

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`.
- Mathlib revision: `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
- Dependency lock: the exact committed `lake-manifest.json`.

```text
lake build MathlibAnnex
lake env lean examples/Import.lean
lake env lean examples/ImportMankiewicz.lean
lake env lean examples/ImportSphereRigidity.lean
lake env lean examples/ImportRosenberg.lean
```

The root library build includes all three Project facades. Release qualification requires an exact source identity check, library build, all four independent imports, compiled-axiom audit, LF blob policy and repository cleanliness. The manual qualification workflow produces a machine receipt and raw logs; it performs no deployment. See [Verification](VERIFICATION.md) for the policy and receipt binding.

## License and corrections

Original MathlibAnnex Lean source, Project import facades, examples, repository software and ordinary technical documentation are licensed under the [Apache License 2.0](LICENSE). External components retain their own terms; see [Third-party notices](THIRD_PARTY_NOTICES.md). This source license does not cover separately published LFH content, Brief Reports, prior-art notes, website editorial content or private Workbench/LFH technology.

No dependency source, compiled cache or external toolchain is vendored. Canonical library source remains in this library rather than being copied into project-owned research repositories. This is AI-assisted material selected and maintained by Ryotaro Tanaka; no novelty or first-formalization claim is made. Report corrections through the repository issue tracker, identifying an exact source revision as described in [Contributing](CONTRIBUTING.md).

Source qualification, source admission, LFH declaration cards and Project views, document correspondence, and website publication have separate records. A build result alone does not establish those other states.

## Sphere Rigidity source in v0.2.0

The v0.2.0 source tree adds the coherent 48-module Sphere Rigidity delta and the comments/imports-only `MathlibAnnex.Projects.SphereRigidity` entry. Its single direct root is `MathlibAnnex.Analysis.Normed.Sphere.MetricRigidity`; exact closure bytes and environment pins are recorded in [the Project Source Manifest](docs/projects/sphere-rigidity.json). The intended source tag is `v0.2.0`. This in-tree description does not assert that the tag or public release exists; actual public commit, tree, tag and qualification identities belong to the external publication record.

```lean
import MathlibAnnex.Projects.SphereRigidity
#check MathlibAnnex.Sphere.nonempty_isometryEquiv_iff_nonempty_linearIsometryEquiv_of_finiteDimensional
```

Formal source admission is separate from Declaration Cards, the Research Companion, document correspondence, LFH publication and website publication. Cards are `NOT_STARTED`; the Research Companion / Progressive Project is `IN_PREPARATION`. Document correspondence is a separate, not-yet-completed axis.
