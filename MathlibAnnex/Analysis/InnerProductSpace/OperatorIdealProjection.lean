/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.SurjectiveRightInverse
import MathlibAnnex.Analysis.InnerProductSpace.OperatorIdeal
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisEmbedding
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Orthogonal projections in algebraic operator ideals

A closed subspace of the literal range of an ideal member has its orthogonal
projection in the same ideal. Projections also transfer downwards in genuine
Hilbert-basis cardinality. Neither result assumes that the ideal is norm-closed
or star-closed. All operators have the original bounded-operator norm.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uK uI uJ


namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [hH : CompleteSpace H]

include hH in
/-- If a closed subspace lies in the literal range, its projection is a two-sided
multiple of the original operator. The right factor is constructed from the
bounded right inverse of the projected surjection. -/
theorem exists_starProjection_mul_mul_eq_of_le_range (T : H →L[𝕜] H)
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (hMT : M ≤ T.range) :
    letI : CompleteSpace M := hM.completeSpace_coe
    ∃ B : H →L[𝕜] H, (M.starProjection * T) * B = M.starProjection := by
  letI : CompleteSpace M := hM.completeSpace_coe
  let A : H →L[𝕜] M := M.orthogonalProjectionOnto.comp T
  have hA : Surjective A := by
    intro y
    obtain ⟨x, hx⟩ := hMT y.property
    change T x = (y : H) at hx
    refine ⟨x, ?_⟩
    change M.orthogonalProjectionOnto (T x) = y
    rw [hx]
    exact M.orthogonalProjectionOnto_mem_subspace_eq_self y
  let R : M →L[𝕜] H := A.orthogonalRightInverse hA
  refine ⟨R.comp M.orthogonalProjectionOnto, ?_⟩
  ext x
  change (M.orthogonalProjectionOnto (T (R (M.orthogonalProjectionOnto x))) : H) =
    (M.orthogonalProjectionOnto x : H)
  exact congrArg (fun z : M => (z : H))
    (A.apply_orthogonalRightInverse hA (M.orthogonalProjectionOnto x))

include hH in
/-- For an isometric embedding of closed subspaces, the ambient sandwich gives
the smaller projection. The adjoint belongs to the ambient operator ring; it
need not belong to an ideal. -/
theorem adjoint_mul_starProjection_mul_eq_of_linearIsometry
    (M N : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    (hN : IsClosed (N : Set H)) (U : N →ₗᵢ[𝕜] M) :
    letI : CompleteSpace M := hM.completeSpace_coe
    letI : CompleteSpace N := hN.completeSpace_coe
    let V : H →L[𝕜] H :=
      M.subtypeL.comp (U.toContinuousLinearMap.comp N.orthogonalProjectionOnto)
    (V.adjoint * M.starProjection) * V = N.starProjection := by
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := hN.completeSpace_coe
  let V : H →L[𝕜] H :=
    M.subtypeL.comp (U.toContinuousLinearMap.comp N.orthogonalProjectionOnto)
  ext x
  apply ext_inner_left 𝕜
  intro y
  change inner 𝕜 y (V.adjoint (M.starProjection (V x))) =
    inner 𝕜 y (N.starProjection x)
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hm : M.starProjection (V x) = V x :=
    Submodule.starProjection_eq_self_iff.mpr (U (N.orthogonalProjectionOnto x)).property
  rw [hm]
  change inner 𝕜 (U (N.orthogonalProjectionOnto y)) (U (N.orthogonalProjectionOnto x)) =
    inner 𝕜 y (N.starProjection x)
  rw [U.inner_map_map]
  change inner 𝕜 (N.starProjection y) (N.starProjection x) =
    inner 𝕜 y (N.starProjection x)
  have ho := Submodule.starProjection_inner_eq_zero (K := N) y
    (N.starProjection x) (N.starProjection_apply_mem x)
  rw [inner_sub_left] at ho
  exact (sub_eq_zero.mp ho).symm

end ContinuousLinearMap

namespace TwoSidedIdeal

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [hH : CompleteSpace H]

include hH in
/-- Luft's projection extraction for an actual algebraic two-sided ideal.
Closedness applies to the subspace, not to the ideal. -/
theorem starProjection_mem_of_le_range (I : TwoSidedIdeal (H →L[𝕜] H))
    {T : H →L[𝕜] H} (hT : T ∈ I) (M : Submodule 𝕜 H)
    (hM : IsClosed (M : Set H)) (hMT : M ≤ T.range) :
    letI : CompleteSpace M := hM.completeSpace_coe
    M.starProjection ∈ I := by
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨B, hB⟩ := T.exists_starProjection_mul_mul_eq_of_le_range M hM hMT
  rw [← hB]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hT)

include hH in
/-- Transfer a projection along an actual isometric embedding of closed
subspaces, with no star-closedness assumption on the ideal. -/
theorem starProjection_mem_of_linearIsometry (I : TwoSidedIdeal (H →L[𝕜] H))
    (M N : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    (hN : IsClosed (N : Set H)) (U : N →ₗᵢ[𝕜] M) :
    letI : CompleteSpace M := hM.completeSpace_coe
    letI : CompleteSpace N := hN.completeSpace_coe
    M.starProjection ∈ I → N.starProjection ∈ I := by
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := hN.completeSpace_coe
  intro hP
  let V : H →L[𝕜] H :=
    M.subtypeL.comp (U.toContinuousLinearMap.comp N.orthogonalProjectionOnto)
  have he : (V.adjoint * M.starProjection) * V = N.starProjection :=
    ContinuousLinearMap.adjoint_mul_starProjection_mul_eq_of_linearIsometry M N hM hN U
  rw [← he]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hP)

include hH in
/-- The cardinal form of projection transfer uses given Hilbert bases in
independent universes, including empty and finite index types. -/
theorem starProjection_mem_of_hilbertBasis_lift_mk_le
    (I : TwoSidedIdeal (H →L[𝕜] H)) (M N : Submodule 𝕜 H)
    (hM : IsClosed (M : Set H)) (hN : IsClosed (N : Set H))
    {ι : Type uI} {κ : Type uJ} (b : HilbertBasis ι 𝕜 N) (c : HilbertBasis κ 𝕜 M)
    (hcard : Cardinal.lift.{uJ} (#ι) ≤ Cardinal.lift.{uI} (#κ)) :
    letI : CompleteSpace M := hM.completeSpace_coe
    letI : CompleteSpace N := hN.completeSpace_coe
    M.starProjection ∈ I → N.starProjection ∈ I := by
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := hN.completeSpace_coe
  obtain ⟨U⟩ := b.nonempty_linearIsometry_of_lift_mk_le c hcard
  exact I.starProjection_mem_of_linearIsometry M N hM hN U

include hH in
/-- The full projection conclusion of Luft Lemma 6.1: every smaller Hilbert
subspace projection belongs to the ideal of the original operator. -/
theorem starProjection_mem_of_lift_mk_le_of_le_range
    (I : TwoSidedIdeal (H →L[𝕜] H)) {T : H →L[𝕜] H} (hT : T ∈ I)
    (M N : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    (hN : IsClosed (N : Set H)) (hMT : M ≤ T.range)
    {ι : Type uI} {κ : Type uJ} (b : HilbertBasis ι 𝕜 N) (c : HilbertBasis κ 𝕜 M)
    (hcard : Cardinal.lift.{uJ} (#ι) ≤ Cardinal.lift.{uI} (#κ)) :
    letI : CompleteSpace N := hN.completeSpace_coe
    N.starProjection ∈ I := by
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := hN.completeSpace_coe
  exact I.starProjection_mem_of_hilbertBasis_lift_mk_le M N hM hN b c hcard
    (I.starProjection_mem_of_le_range hT M hM hMT)

end TwoSidedIdeal
