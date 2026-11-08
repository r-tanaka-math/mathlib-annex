# Finite-amplification proof sources

Two proofs in [FiniteAmplification.lean](../../MathlibAnnex/Analysis/VonNeumannAlgebra/FiniteAmplification.lean) adapt arguments from the Apache-2.0 [FiniteInterpolation source at v0.6.0](https://github.com/r-tanaka-math/mathlib-annex/blob/5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e/MathlibAnnex/Analysis/CStarAlgebra/FiniteInterpolation.lean).

The cyclic-subspace proof replaces the irreducibility and scalar-block argument with commutation of each projection block. It handles the subsingleton fiber separately. The approximation proof invokes the resulting bicommutant theorem and uses the coordinate norm estimate. The [declaration crosswalk](adaptations.json) gives the source and target declarations, commit, Git blob, file SHA-256 values and changes. The third proof in the module transfers approximation from the norm closure through existing APIs.

The [license text](../../LICENSE), [v0.6.0 notices](history/Annex-v0.6.0-THIRD_PARTY_NOTICES.txt) and [original W01 notice](history/W01-A-NOTICES.md) preserve the upstream terms and attribution. Paths named in the historical notices describe the original packages. The links above resolve in this distribution.
