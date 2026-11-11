# MathlibAnnex v0.6.2

MathlibAnnex is a Lean library of reusable mathematical declarations. This
release uses Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` in the unchanged dependency lock.

Use the Glimm–Sakai entry for the internal type I, GCR and literal bidual
equivalences, and the von Neumann entry for projection theory and type decomposition:

```lean
import MathlibAnnex.Projects.GlimmSakai
import MathlibAnnex.Projects.VonNeumannTypeDecomposition
```

The nine [Project manifests](docs/projects/MATHLIBANNEX_PROJECT_SOURCE_MANIFESTS.json)
cover Mankiewicz, Sphere Rigidity, Rosenberg, Pure State Homogeneity, Naimark,
Geometric Structure Spaces, Lipschitz-homeomorphic Banach Spaces, Glimm–Sakai,
and Von Neumann Type Decomposition. Each manifest identifies the imports-only
entry, direct roots and complete source closure. Independently compiled
production modules outside an entry, Audit modules and consumers remain included.

Owner-final qualification passed 21 checks over 1,138 targets and 21,056
compiled declarations, including 2,304 Glimm–Sakai task declarations. The
qualified internal version was 0.7.0; the release version is 0.6.2.
See [current verification](VERIFICATION.md) for the original run and exact
qualification inheritance. Regular private source admission and the scoped
[owner source grant](docs/releases/v0.6.2-source-permission.md) are recorded.
The final public commit, tree, archive hashes and publication readback are
recorded in the release assets. Authorization recorded in the source metadata
is distinct from that publication-event record.

The [license](LICENSE) and [third-party notices](THIRD_PARTY_NOTICES.md) retain
the original terms and attribution. Production-time candidate labels in Lean
headers and historical notices remain unchanged; the later exact grant is
explained in the permission record. Earlier release evidence is linked in the
historical section of Verification and the preserved [Changelog](CHANGELOG.md).
