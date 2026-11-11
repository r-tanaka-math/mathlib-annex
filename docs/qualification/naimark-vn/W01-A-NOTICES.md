# Source attribution and retained notices

This return contains newly authored source candidates and typed consumers.
Existing Mathlib and MathlibAnnex modules are imported, not redistributed as
replacement source files. Their original terms remain unchanged.

## Retained upstream documents

- `LICENSES/Apache-2.0.txt` is the exact `LICENSE` from
  [mathlib-annex at the pinned commit](https://github.com/r-tanaka-math/mathlib-annex/blob/5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e/LICENSE).
- `LICENSES/Annex-THIRD_PARTY_NOTICES.md` is the exact upstream
  [THIRD_PARTY_NOTICES.md](https://github.com/r-tanaka-math/mathlib-annex/blob/5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e/THIRD_PARTY_NOTICES.md).
  Its relative links refer to the upstream repository; that repository is not vendored here.

The unchanged source identities and document hashes are recorded in
`REFERENCES_ACTUAL_READ.json`; the delivered copies are covered by `MANIFEST.json`.

## Adapted proof source

The first two declarations of
`delta/MathlibAnnex/Analysis/VonNeumannAlgebra/FiniteAmplification.lean`
adapt parts of these Apache-2.0 upstream proofs:

|Upstream declaration|New declaration|
|---|---|
|`StarAlgHom.diagonal_apply_mem_cyclicSubspace_of_irreducible`|`StarAlgHom.diagonal_apply_mem_cyclicSubspace_of_mem_bicommutant`|
|`StarAlgHom.exists_atomic_apply_sub_norm_lt_of_irreducible`|`StarAlgHom.exists_forall_apply_sub_norm_lt_of_mem_bicommutant`|

Exact upstream source:
[FiniteInterpolation.lean](https://github.com/r-tanaka-math/mathlib-annex/blob/5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e/MathlibAnnex/Analysis/CStarAlgebra/FiniteInterpolation.lean),
repository `r-tanaka-math/mathlib-annex`, commit
`5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e`,
Git blob `339840f25ba39dda073d17c76df04fd6bc5ce17b`.

The adaptation retains the standard Hilbert sum, cyclic projection, finite
block expansion, and metric approximation route. It replaces the
irreducibility/Schur/scalar-block step with direct commutation between the
target operator and every projection block. The resulting theorem has a
bicommutant-membership premise and does not assume irreducibility or a
nonzero Hilbert space. The original irreducible theorem is not applied as a
general bicommutant theorem.

The third finite-amplification declaration uses the existing norm closure
and standard closed-star-subalgebra instances to transfer approximation
back to the original, possibly nonclosed, star subalgebra.

## Mathematical route and ordinary API reuse

The classical finite-amplification proof route is described in the supplied
dispatch `MATH/PROOF_ROUTES_JA.md` and restated in our own words in
`REPORT_JA.md`. No full textbook or paper text is reproduced.
`PROVENANCE.json` separates proof adaptation, ordinary imported-API
composition, and typed consumers, with a record for every authored declaration.

## Release boundary

This source return does not make an owner grant for public release of the
new contribution, certify Annex admission, or alter any upstream notice.
Any later publication and exact-scope licensing decision remains a
separate owner action under the dispatch contract.
