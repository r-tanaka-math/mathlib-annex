# MathlibAnnex v0.6.0

MathlibAnnex is a Lean library of reusable mathematical declarations. It builds with Lean 4.35.0 and the Mathlib revision in the package lock. To use the almost-isometric Banach-space result, import its Project entry.

```lean
import MathlibAnnex.Projects.LipschitzHomeomorphicBanachSpaces
```

The seven [Project manifests](docs/projects/MATHLIBANNEX_PROJECT_SOURCE_MANIFESTS.json) identify each entry, its direct imports and its source closure. The Lip entry reaches 159 of 166 production modules. The library also retains seven independently compiled modules outside that entry. Audit and consumer modules exercise the library separately.

Owner-final qualification passed 17 checks across 928 targets. The declaration census covered 18,448 declarations. See [Verification](VERIFICATION.md), [third-party notices](THIRD_PARTY_NOTICES.md) and the [v0.5.0 release history](docs/releases/v0.5.0.md).
