# Source attribution and release boundary

This return contains newly authored source candidates and typed consumers. Fixed Mathlib, public MathlibAnnex, and accepted Naimark L01 modules are imported and remain external read-only providers. Their source bodies are not distributed here as replacement modules.

The one required other-lane source, B's `Enveloping/NormalExtension.lean`, is
included unchanged under `providers/B/` for independent supply validation.
It is not C-authored source and is not counted in C's declaration census.
Its exact archive member, SHA256 and source signatures are recorded in
`EVIDENCE/B_PROVIDER.json`. The source archive is
`GLIMM_SAKAI_CHAT_B_W01_RETURN.zip`, SHA256
`9cfa5339af66e2ef27e7252ff5463ca77654967b231280504b1e6d22fe563753`.
B's statement that new exact-source public release permission remains
pending is retained; this delivery supplies no new publication grant.

C `TypeI/Representation.lean` applies B's
`MathlibAnnex.RepresentedBidual.extension_mem_vonNeumannAlgebra` and
`MathlibAnnex.RepresentedBidual.intertwines_extension`. The former duplicate
landing and coefficient-intertwining arguments have been removed from C.
These are ordinary API applications, with a canonical inclusion wrapper,
not ports of the B proofs.

## Retained upstream terms

`LICENSES/Apache-2.0.txt` and `LICENSES/Annex-THIRD_PARTY_NOTICES.md` are copied byte-for-byte from the read-only dispatch's accepted-provider notices. The Apache text is the pinned Annex license. The notice's relative links refer to its original upstream repository. These documents do not grant permission to publish this new exact contribution.

The complete fixed refs, original file paths, Git blob identities, SHA256 values when full bytes were read, and actual-read scopes are recorded in `EVIDENCE/PROVIDERS_ACTUAL_READ.json`. Imported source is separated from adapted proof source in `PROVENANCE.json`.

## Bundled accepted Naimark L01 origin

The accepted Naimark L01 provider has source kind `BUNDLED_ACCEPTED_RETURN`
and source repository identity `r-tanaka-math/mathlib-annex-staging`.
Its checkpoint is `cb132134c0f7f011aee3e962616bd1b4701b55eb`, tree
`3df81f7eab48bba8f8b7336efc079129ea3c6f62`. The accepted archive's
`git/checkpoint.json` records this checkpoint as `LOCAL_UNSYNCED`.

The retrieved object is the immutable input archive
`NAIMARK_VN_LOCAL_L01_RETURN.zip`, SHA256
`6bcb94567b6301c10c404e7bf77d5401107cb42c24c715cbdd0c2ac8dc319ea9`.
Each source locator identifies its exact `source/...` member and source
SHA256. The archive was supplied by the initial dispatch; this return does
not claim an independent public-repository fetch of that checkpoint.
`EVIDENCE/PROVENANCE_REPAIR.json` records byte equality for all 30 source
members, including the 19 production modules and 11 accepted consumers.
These read-only providers are not new contributions of this return.

The faithful-trace proof-route origin is archive member
`source/MathlibAnnex/Analysis/VonNeumannAlgebra/Finite.lean`, SHA256
`801c17f06c237269bafe0e81a254bbb895489346fe8b341e856b3f662daa69dc`.
Its original declaration is
`LinearMap.mul_star_self_eq_one_of_faithful_tracial`.
The local-checkpoint attribution preserves the bundled original terms and
all retained upstream notices. It supplies no new public license grant for
an exact contribution. `PROVENANCE.json` identifies the adaptation;
`DEPENDENCIES.json` and `EVIDENCE/PROVIDERS_ACTUAL_READ.json` use the same
archive-based identity and preserve the historical actual-read scopes.

## Adapted mathematical proofs

The arbitrary-index summability and strong-limit construction in `Projection/OrthogonalSum.lean` generalizes the pointwise orthogonal-series proof in:

- Repository: `r-tanaka-math/mathlib-annex`.
- Commit: `5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e`.
- Path: `MathlibAnnex/Analysis/InnerProductSpace/OrthogonalSum.lean`.
- Original declarations: the private `summable_apply_of_orthogonal_of_bound` and public `exists_strongLimit_of_orthogonal_of_bound`.

The original argument uses natural-number prefix sums. The new argument uses arbitrary index types and the net of finite subsets; it retains the Hilbert-space squared-norm summability route. Existing strong-product and adjoint-limit proofs are imported unchanged. The new theorem additionally establishes the partial-isometry identities, internal VN membership, and both support limits.

The faithful-tracial-functional finite-projection theorem in `Projection/Finite.lean` generalizes the accepted L01 proof `LinearMap.mul_star_self_eq_one_of_faithful_tracial` from the unit defect `1 - v * star v` to a general projection defect. The accepted `IsFinite` definition and its theorems are unchanged. Its exact provider file identity is recorded in `DEPENDENCIES.json` and the adaptation is attributed in `PROVENANCE.json`.

Other proofs are newly authored arguments or compositions/specializations of the exact imported APIs. The actual represented-bidual, Schur, projection, Hilbert-sum, and C*-algebra providers retain their upstream authorship and terms. No author, DOI, or publication permission is inferred. No long textbook or paper passage is reproduced.

## New contribution

The intended release license for newly authored source is Apache-2.0, subject to the owner's decision for the exact public source identity. This source-only return neither publishes the contribution nor certifies Annex admission or a kernel result.

## Internal finite-dimensional descent

`TypeI/FiniteDimensional.lean` adapts the natural-number dimension-minimization
proof route of `NonUnitalCStarRepresentation.exists_isMinimalStarProjection_le`
in `MathlibAnnex/Analysis/CStarAlgebra/Ideal/MinimalCompactCorner.lean`, public
Annex commit `5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e`. The pinned header's
Ryotaro Tanaka copyright, author and Apache notice are retained verbatim in
the new source header. The new argument uses the finite-dimensional algebra
and the ranges of internal left multiplication, without imposing finite
dimension on the ambient Hilbert space or a compact representation.

The proper-infiniteness extension reuses the existing C shift-family proof
through an explicit public wrapper addition; it does not copy that recursive
proof into the new module. Arbitrary orthogonal sums and support identities
remain applications of the frozen C providers.
