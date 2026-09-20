# Proposed v0.4.0 naming migration

This is an unbuilt private candidate, not a release receipt. It contains the
renamed source for all five Project facades. Ordinary Git ancestry and all
historical release identities must be retained. The candidate source may be
committed as an ordinary successor of public commit
`a5f98f86e43ff2c68fd0793f08e55dcd64cdc979`, using the selected source content from
private snapshot `cb3eb37c9b15a0781e38415a72fd6f0463f4d28f` as provenance, without
publishing private orchestration or rebasing old public history.

A full new-source build is required, not a history reset. Never rewrite a public
tag or old source/LFH/PDF asset to make it mean this source. Renamed declarations
receive explicit successor relations under the existing LFH identity rules;
review records are not silently transplanted. Proposed v0.4.0 is a breaking
pre-1.0 API update, not v0.3.1 and not a claim of a stable v1.0 API.

In-tree manifests bind content and pending requirements. The containing commit
and tree, successful local receipts and hosted run receipt are external bindings,
so a commit/hash cycle is avoided. All five Project closures and all eleven
workflow checks have been regenerated, but their native Lean execution remains
pending. Import scanning performed while preparing this candidate is static only.

Nothing in this file authorizes a public push, tag, Release, source admission,
workflow execution, Card/Catalog/Project publication or website change.
