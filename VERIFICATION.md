# Source qualification for v0.6.2

## Current qualification

[Owner-final run 42932125221](https://github.com/r-tanaka-math/mathlib-annex-staging/actions/runs/42932125221),
attempt 1, job 130233208577, passed all 21 required checks for commit
`e81ace1cc133d9e765000d063610c4dc234ec545`, tree `8becc4e38642b72353a93786ee071872ee291bca`.
The Linux final run restored 1,138 exact native checkpoints. Its 1,126-module
census and twelve facades cover nine Project entries, validation consumers and
21,056 compiled declarations, including 2,304 Glimm–Sakai task declarations.
There are no compiled axioms outside `propext`, `Classical.choice` and `Quot.sound`.
This is checkpoint-assisted qualification, not a claim of 1,138 fresh builds.

The [current qualification summary](docs/qualification/owner-final.json) names
this run and the original receipt and seal hashes. Its qualified internal
package version is 0.7.0; the current package version is 0.6.2. The previously
verified version-only successor and this metadata repair preserve all 1,157
public Lean source files, pins, lock, targets, flags, providers and import
closures. The fixed Lake configuration and search-path comparison from the
version-only step is inherited unchanged: this repair does not change
`lakefile.toml`, the lock, toolchain or build configuration. No new Lean compile
or second owner-final run is required or performed for this metadata repair.

Regular private source admission is an actual Workbench source import and
readback, separate from workflow qualification. The
[exact owner grant](docs/releases/v0.6.2-source-permission.md) covers new Lean
contributions only to the extent the owner may license them. Third-party terms
remain effective. Publication events and final public identities are recorded
separately in the release assets. Controller Lean execution
is NOT_RUN; accepted Windows and hosted Linux executions keep their original
identities. Release assets bind the new projection commit, tree and
ZIP to the original qualification, grant and actual admission receipts; these
identities are external to avoid embedding a commit into its own tree.

## Historical release evidence

The following are historical records, not the current qualification summary:

- [v0.6.1 Verification at the exact public parent](https://github.com/r-tanaka-math/mathlib-annex/blob/c05416f17362be14582ab1bce7d70b41aab6dffc/VERIFICATION.md)
  records the published Naimark and von Neumann extension (958 targets).
- [v0.6.0 Verification at its release tag](https://github.com/r-tanaka-math/mathlib-annex/blob/v0.6.0/VERIFICATION.md)
  records the Lipschitz-homeomorphic Banach Spaces release (928 targets,
  18,448 declarations and 17 checks).
- [v0.5.0 release record](docs/releases/v0.5.0.md) and the complete public
  [Changelog](CHANGELOG.md) preserve earlier history.

Historical receipts, notices and candidate-time PENDING labels are retained as
original evidence. They do not override the current, narrowly scoped source
grant and private admission records.
