# MathlibAnnex verification

## Exact qualification contract

The release record must bind the exact MathlibAnnex commit and tree to a successful qualification receipt. A receipt for another source tree does not qualify this version, even when the difference consists only of documentation, licensing or package metadata.

The `Manual release qualification` workflow requires all of the following checks independently:

1. Exact commit, tree, workflow, Lean toolchain, Mathlib revision and dependency-lock identity.
2. The `MathlibAnnex` library build, including the Project import facade.
3. The independent root-import example, `examples/Import.lean`.
4. The independent Mankiewicz Project-entry example, `examples/ImportMankiewicz.lean`.
5. The independent Sphere Rigidity Project-entry example, `examples/ImportSphereRigidity.lean`.
6. A compiled-axiom audit rooted at `MathlibAnnex`, allowing exactly `propext`, `Classical.choice` and `Quot.sound`.
7. The committed-blob LF policy and clean tracked files, index and working tree after qualification.

The pinned environment is `leanprover/lean4:v4.32.0-rc1`, Mathlib `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, and the committed `lake-manifest.json`. The workflow and helper preserve separate results for identity, build, root import, each Project import, compiled-axiom audit, LF blob policy and cleanliness. Missing, skipped, cancelled or failed required checks do not constitute a successful qualification.

## Publication-record binding

The external publication record supplies the actual repository identity, immutable tag and commit/tree identities, source archive identity, workflow run and attempt, successful `qualification.json` receipt and artifact hashes, and release asset identities. These fields must be populated from observed publication and qualification evidence. They are not inferred from a version string or a moving branch.

The [Mankiewicz Project Source Manifest](docs/projects/mankiewicz.json) is an in-tree source-content record: its entry and closure hashes, direct-root and resolved-closure digests, environment pins and axiom policy can be verified without knowing its containing Git commit. The external publication record binds that manifest's exact bytes to the immutable source release and its successful receipt. This avoids a circular Git identity.

## Scope of the evidence

The Project facade contains comments and imports only; it adds no mathematical declarations or copied proofs. Its resolved source closure is explicit in the manifest. Qualification checks source and compiled artifacts; it does not establish mathematical novelty or document-to-formal-source correspondence.

The preserved manual workflow is restricted to private-repository qualification and performs no deployment. Its receipt flags describe actions performed by that workflow: a `license_grant` value of false means the workflow performs no licensing act and does not override the repository [LICENSE](LICENSE). Owner acceptance, LFH source–exposition correspondence, LFH publication and website publication remain separately recorded acts.

Independent `leanchecker` and `nanoda` execution requires a separately qualified resource profile and is outside this workflow's checks.

## Sphere Rigidity v0.2.0 source qualification boundary

The `0.2.0-rc.1` predecessor binds the exact 48-module delta, entry parser result, direct root and content-addressed 48-module closure. Its 13 authority-listed Lean blobs are LF-normalized; the older BuildResult is pre-repair evidence only. Private GitHub run `35080624090` (attempt 1) succeeded for predecessor commit `18519611549f0aac228f03aa11dbdfd3cb0d6f06`, tree `ad93d8d6856d0ff955f92b42dcedc8e6f35a5838`: the build completed 8,637 jobs; root, Mankiewicz and Sphere Rigidity imports passed; the compiled-axiom audit passed for 2,016 declarations with the stated allowlist; LF blob policy and cleanliness passed.

That run is prior exact RC evidence, **not** qualification of this final `0.2.0` source tree. Before any public `v0.2.0` act, the owner must manually qualify the final commit/tree with the unchanged private workflow. The resulting final run ID, attempt, machine receipt, artifact hash and compiled-axiom result must be observed and bound by a later external publication record. No final-tree run ID or public release identity is asserted in this file.
