# MathlibAnnex v0.5.0 verification

## Current accepted qualification

Run `38063627833`, attempt `1`, qualified commit
`4d4cfc1b2b5a2642a6a90d3fc5c4e6f4f8abdfa4` and tree
`2df11956be5a3b1c55827c291d74bfc03cd6727c` on Linux. All 14 mandatory gates passed:

- `build`: PASS.
- `cleanliness`: PASS.
- `compiled_axiom_audit`: PASS.
- `complete_source_coverage`: PASS.
- `downstream_import`: PASS.
- `gss_project_entry_import`: PASS.
- `gss_public_census`: PASS.
- `identity`: PASS.
- `naimark_entry_import`: PASS.
- `project_entry_import`: PASS.
- `project_entry_parser`: PASS.
- `pure_state_homogeneity_entry_import`: PASS.
- `rosenberg_entry_import`: PASS.
- `sphere_rigidity_entry_import`: PASS.

All 739 source targets are accounted for: 312 `CHECKPOINT_RESTORED`, 427 `FRESH`,
and zero qualification inherited merely from a cache hit. The 732 library modules,
six imports-only facades and root are covered. Native successful outputs were
bound to source, compiler, Linux platform, flags, dependency output hashes and
their original producer run/attempt. Historical intermediate `AXIOM_PENDING`
receipts are unchanged; the final successful receipt supplies the separate audit.
The module-origin census records 14,281 declarations (6,029 GSS), checks all
3,252 public GSS names, and permits only `propext`, `Classical.choice`, `Quot.sound`.

Lean is `leanprover/lean4:v4.32.0-rc1`, Mathlib is
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`; all nine locked dependencies remain exact.
The unchanged workflow has ten ordered native stages (base, seven GSS, other,
final) and a separate lightweight failure-report path. It is manually triggered
and does not deploy. Ordinary compilations use `-j 1 -M 4096`; the exact plan
retains the bounded DiscreteCCR and CompactRepresentationRigidity exceptions.
Resource guards, artifact guards and required gates remain unchanged.

## Metadata-only publication binding

The qualified identity above is not rewritten to the public identity. This bounded
v0.5.0 publication changes only twelve release documents/metadata files. All 756
Lean files, pins, workflow/helpers, 739 targets, fourteen gates, module keys and
type/axiom evidence remain identical. Under the owner's explicit v0.5.0 authority
and qualification-reuse rule, this metadata-only projection reuses the exact
formal qualification; it does not require another full Lean build.

The Release assets `PUBLICATION_RECORD.json` and `SOURCE_RELEASE_MANIFEST.json`
record the new public commit/tree, sole public-main parent, annotated tag, source
inventory and hashes, and the qualified-to-public mapping. The exact original
`GITHUB_QUALIFICATION_RECEIPT.json` retains its historical `formal_public_admission=false`,
`owner_acceptance=false` and `public_deployment=NOT_PERFORMED`: that workflow
performed no publication. The later owner-authorized source publication is a
separate act. In-tree manifests bind source bytes; containing Git identities live
in the external record to avoid self-referential hashes.

The limited public qualification-evidence ZIP supplies the original receipt,
catalog, gate summary and parser/import evidence. Full original native logs,
outputs and census are preserved in a private permanent archive, independently
of Actions expiration, with exact identities in the publication record.

## Explicit limits

Independent single-runner clean qualification: `NOT_RUN`. Full Mathlib rebuild
without cache: not performed. Full-paper source/exposition semantic review,
independent leanchecker/nanoda execution, novelty certification, LFH publication
and website updates are outside this source release. Normal Lean kernel acceptance
and compiled-axiom audit establish their stated formal checks only.

## Historical preparation contracts (unchanged text)

The following text is the preserved pre-publication record from the qualified R9
source. Its pending/unbuilt labels, earlier gate counts and unconditional
metadata-rebuild rule describe those earlier candidate contracts. They are not
the current v0.5.0 status. The bounded metadata-only exception above supersedes
that old rebuild rule only for this exact unchanged formal source projection.

---

# Naming-migration qualification status

This v0.4.0 candidate has **not yet passed a Lean build or hosted qualification**.
All prior results described below qualify only their explicitly identified old
source trees. They do not qualify this renamed tree.
The required new workflow checks are listed in
`docs/projects/MATHLIBANNEX_PROJECT_SOURCE_MANIFESTS.json`; they include root and
all five Project-entry consumers, the pinned Lean parser, compiled-axiom audit,
exact identities and cleanliness. Local semantic name/type/data/attribute/instance
comparison and complete import/declaration accounting are additional Workbench gates.
Only the owner may manually dispatch the private workflow. Publication is separate.

The sections below are preserved historical contract/evidence context.
They must not be read as current qualification of this candidate.

---

# MathlibAnnex verification

## Exact qualification contract

The release record must bind the exact MathlibAnnex commit and tree to a successful qualification receipt. A receipt for another source tree does not qualify this version, even when the difference consists only of documentation, licensing or package metadata.

The `Manual release qualification` workflow requires all of the following checks independently:

1. Exact commit, tree, workflow, Lean toolchain, Mathlib revision and dependency-lock identity.
2. The `MathlibAnnex` library build, including the Project import facade.
3. The independent root-import example, `examples/Import.lean`.
4. The independent Mankiewicz Project-entry example, `examples/ImportMankiewicz.lean`.
5. The independent Sphere Rigidity Project-entry example, `examples/ImportSphereRigidity.lean`.
6. The independent Rosenberg Project-entry example, `examples/ImportRosenberg.lean`.
7. A compiled-axiom audit rooted at `MathlibAnnex`, allowing exactly `propext`, `Classical.choice` and `Quot.sound`.
8. The committed-blob LF policy and clean tracked files, index and working tree after qualification.

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

## Rosenberg v0.3.0 private-candidate boundary

The candidate reuses the exact qualified 60-module Rosenberg source and adds source-release integration, an imports-only facade, manifest, independent import example, and v3 workflow receipt. Local qualification must pass on the exact frozen candidate. Hosted qualification remains pending until the owner manually dispatches the private workflow with the exact returned commit/tree values. No public repository write, tag, Release, Card/Catalog/Project publication, or website change is performed by candidate staging.

## Segmented candidate qualification (receipt v5)

Candidate 0.5.0 retains the eleven existing required checks and adds GSS independent entry import, all 3252 public-name/module matches, and complete source coverage. `docs/qualification/segmented-plan.json` assigns all 739 library/Project/root source modules once in dependency order. A missing, skipped, cancelled, failed, foreign-platform or differently bound stage fails final qualification.

Each job has a 330-minute hard limit and a 300-minute soft deadline measured from pre-setup identity. Native Lean is run sequentially with `-j 1 -M 4096`. Only exact pinned Mathlib dependency cache is eligible; Annex outputs are generated natively in this Linux run. Verified delta artifacts bind each output to source hashes, prior local import output hashes, compiler identity, the containing commit/tree, workflow/helper/plan/lock hashes and run ID/attempt. `.olean.private`, `.olean.server` and `.ir` are preserved when generated, together with the main `.olean` and optional `.ilean`. No Lake success trace is fabricated.

The final stage retains whole-root and all five existing independent Project checks, adds GSS import, validates all six facades with the pinned Lean parser, and checks exact manifest closures. The whole-library module-origin census records types, levels, instances, simp status and dependencies and rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound`. Inspection data is streamed separately from compiler stdout; both are preserved. Failed final checks retain already completed outcomes.

The receipt schema is `docs/qualification/github-release-qualification-receipt-v5-segmented.schema.json`. A successful segmented run qualifies only this mode and exact source identity. Independent single-runner clean qualification and full-paper semantic review are separate NOT_RUN claims. Manual dispatch requires verified included execution/storage budget and an existing stop on additional charges. The workflow uses ordinary GitHub-hosted Linux runners, no scheduled/push trigger and three-day artifact retention. Before upload, measured payload bytes plus a conservative ZIP bound and verified prior reservations must stay within the fixed 1,500,000,000-byte cumulative budget; excess refuses upload. Before downloading prior artifacts, their actual same-run identity and expires_at must provide at least the current job timeout of remaining life. This does not guarantee unlimited queue time. This source document does not assert that any dispatch, receipt, staging save or public release has occurred.
