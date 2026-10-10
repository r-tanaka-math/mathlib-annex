/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisEmbedding
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinality
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Closed Hilbert subspaces of prescribed cardinal dimension

A cardinal bounded by the index cardinality of an actual Hilbert basis is
realized by the closed range of an explicitly constructed linear isometry.
The proof uses the Hilbert basis on an `ℓ²` space and an embedding of basis
indices. It never replaces Hilbert dimension by Hamel rank or `finrank`.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uI

namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [hH : CompleteSpace H]
variable {ι : Type uI}

include hH in
/-- A cardinal below the index cardinality of an actual Hilbert basis is
realized by a norm-closed submodule with an actual Hilbert basis of exactly
that cardinality. The ambient basis index and the prescribed cardinal may
live in different universes. -/
theorem exists_closed_submodule_hilbertBasis_mk_eq
    (b : HilbertBasis ι 𝕜 H) (γ : Cardinal.{uH})
    (hγ : Cardinal.lift.{uI} γ ≤ Cardinal.lift.{uH} (#ι)) :
    ∃ (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
      (w : Set M) (c : HilbertBasis w 𝕜 M), #w = γ := by
  have hindex : Cardinal.lift.{uI} (#γ.out) ≤ Cardinal.lift.{uH} (#ι) := by
    simpa only [Cardinal.mk_out] using hγ
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hindex
  let bγ : HilbertBasis γ.out 𝕜 (lp (fun _ : γ.out => 𝕜) 2) := default
  let U : (lp (fun _ : γ.out => 𝕜) 2) →ₗᵢ[𝕜] H := bγ.linearIsometryOfIndexEmbedding b f
  let M : Submodule 𝕜 H := LinearMap.range U.toLinearMap
  have hM : IsClosed (M : Set H) := by
    have hrange : (M : Set H) = Set.range U := by
      ext y
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, hx⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    rw [hrange]
    exact U.isometry.isUniformInducing.isComplete_range.isClosed
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 M
  let e : (lp (fun _ : γ.out => 𝕜) 2) ≃L[𝕜] M :=
    U.toContinuousLinearMap.equivRange U.injective hM
  have he := bγ.lift_mk_eq_of_continuous_linear_equiv c e
  refine ⟨M, hM, w, c, ?_⟩
  simpa only [Cardinal.lift_id, Cardinal.mk_out] using he.symm

include hH in
/-- Same-universe specialization of
`exists_closed_submodule_hilbertBasis_mk_eq`. -/
theorem exists_closed_submodule_hilbertBasis_mk_eq_of_le
    {ι : Type uH} (b : HilbertBasis ι 𝕜 H) (γ : Cardinal.{uH})
    (hγ : γ ≤ #ι) :
    ∃ (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
      (w : Set M) (c : HilbertBasis w 𝕜 M), #w = γ := by
  exact b.exists_closed_submodule_hilbertBasis_mk_eq γ
    (by simpa only [Cardinal.lift_id] using hγ)

end HilbertBasis
