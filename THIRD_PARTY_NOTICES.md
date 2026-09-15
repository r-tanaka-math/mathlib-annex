# Third-party notices

Lean and Lake, Mathlib and its transitive dependencies, and the pinned GitHub Actions used for qualification are external components, not vendored in this source tree. They remain governed by their own licenses and notices; MathlibAnnex's Apache License 2.0 does not relicense them.

## Toolchain and dependencies

- Lean/Lake: `leanprover/lean4:v4.32.0-rc1`.
- Mathlib: `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
- Transitive dependencies recorded in `lake-manifest.json`: Cli, LeanSearchClient, Qq, aesop, batteries, importGraph, plausible and proofwidgets.

The dependency lock records exact repositories and revisions. Consult each component's upstream license and notice files at the locked revision. Exact available upstream license texts and their hashes are retained in the release dossier; they are not dependency source bundled into this library.

## Qualification actions

The unchanged workflow pins these external actions:

- `actions/checkout@34e114876b0b11c390a56381ad16ebd13914f8d5`
- `leanprover/lean-action@50fcf42d2e460296f1a34b402e990d1b24f8b596`
- `actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02`

Each action's upstream terms apply independently. Action revision pins identify the code used for qualification; they do not imply that an action is vendored or covered by the MathlibAnnex license.
