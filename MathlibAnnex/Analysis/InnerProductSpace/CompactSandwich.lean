/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.ConjugateAdjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness under the actual adjoint sandwiches

The linear and conjugate-linear sandwiches are the existing constructions.
In the second case both outer factors are conjugate-linear, and the resulting
operator is linear. Mathlib's compact-operator composition lemmas already accept
continuous semilinear maps, so no antilinear map is coerced to a complex-linear map.
The inverse sandwiches are justified by the actual coefficient identities, including
conjugation, rather than by asserting that every closed ideal is invariant.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace InnerProductSpace

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Forward preservation needs bounded linear factors, not their invertibility. -/
theorem isCompactOperator_adjointSandwich (U V : H →L[𝕜] K)
    {b : K →L[𝕜] K} (hb : IsCompactOperator b) :
    IsCompactOperator (adjointSandwich U V b) :=
  (hb.comp_clm U).clm_comp V.adjoint

/-- Two bounded conjugate-linear factors sandwich a compact linear operator to a
compact linear operator. The intermediate composition is genuinely semilinear. -/
theorem isCompactOperator_conjugateAdjointSandwich (U V : H →L⋆[𝕜] K)
    {b : K →L[𝕜] K} (hb : IsCompactOperator b) :
    IsCompactOperator (conjugateAdjointSandwich U V b) :=
  (hb.comp_clm U).clm_comp (conjugateAdjoint V)

/-- The forward sandwich cancels the sandwich constructed from the actual inverses. -/
theorem adjointSandwich_apply_symm (U V : H ≃L[𝕜] K) (a : H →L[𝕜] H) :
    adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap
      (adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap a) = a :=
  leftInverse_of_inner_semilinear_transport (σ := RingHom.id 𝕜)
    U.toLinearEquiv V.toLinearEquiv
    (adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (inner_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (inner_adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap) a

/-- Cancellation in the other direction. -/
theorem adjointSandwich_symm_apply (U V : H ≃L[𝕜] K) (b : K →L[𝕜] K) :
    adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap
      (adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap b) = b := by
  simpa using adjointSandwich_apply_symm U.symm V.symm b

/-- The two conjugations in the coefficient identities cancel in the inverse sandwich. -/
theorem conjugateAdjointSandwich_apply_symm (U V : H ≃SL[starRingEnd 𝕜] K)
    (a : H →L[𝕜] H) :
    conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap
      (conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap a) = a :=
  leftInverse_of_inner_semilinear_transport (σ := starRingEnd 𝕜)
    U.toLinearEquiv V.toLinearEquiv
    (conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (inner_conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (inner_conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap) a

/-- Cancellation for the conjugate-linear pair in the other direction. -/
theorem conjugateAdjointSandwich_symm_apply (U V : H ≃SL[starRingEnd 𝕜] K)
    (b : K →L[𝕜] K) :
    conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap
      (conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap b) = b := by
  simpa using conjugateAdjointSandwich_apply_symm U.symm V.symm b

/-- With bounded inverses, compactness is both preserved and reflected. -/
theorem isCompactOperator_adjointSandwich_iff (U V : H ≃L[𝕜] K) (b : K →L[𝕜] K) :
    IsCompactOperator (adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap b) ↔
      IsCompactOperator b := by
  constructor
  · intro h
    have h' := isCompactOperator_adjointSandwich
      U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap h
    simpa only [adjointSandwich_symm_apply] using h'
  · exact isCompactOperator_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap

/-- Reflection is also valid for the conjugate-linear pair, without a scalar-change
replacement of the compactness predicate. -/
theorem isCompactOperator_conjugateAdjointSandwich_iff
    (U V : H ≃SL[starRingEnd 𝕜] K) (b : K →L[𝕜] K) :
    IsCompactOperator
      (conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap b) ↔
      IsCompactOperator b := by
  constructor
  · intro h
    have h' := isCompactOperator_conjugateAdjointSandwich
      U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap h
    simpa only [conjugateAdjointSandwich_symm_apply] using h'
  · exact isCompactOperator_conjugateAdjointSandwich
      U.toContinuousLinearMap V.toContinuousLinearMap

/-- Equality of the actual compact-operator families for a bounded linear pair. -/
theorem image_adjointSandwich_setOf_isCompactOperator (U V : H ≃L[𝕜] K) :
    adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
      {b : K →L[𝕜] K | IsCompactOperator b} =
        {a : H →L[𝕜] H | IsCompactOperator a} := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact isCompactOperator_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap hb
  · intro ha
    refine ⟨adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap a,
      isCompactOperator_adjointSandwich
        U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap ha,
      adjointSandwich_apply_symm U V a⟩

/-- Equality of compact families for a bounded conjugate-linear pair. This does not
assert invariance of arbitrary closed operator ideals. -/
theorem image_conjugateAdjointSandwich_setOf_isCompactOperator
    (U V : H ≃SL[starRingEnd 𝕜] K) :
    conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
      {b : K →L[𝕜] K | IsCompactOperator b} =
        {a : H →L[𝕜] H | IsCompactOperator a} := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact isCompactOperator_conjugateAdjointSandwich
      U.toContinuousLinearMap V.toContinuousLinearMap hb
  · intro ha
    refine ⟨conjugateAdjointSandwich
      U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap a,
      isCompactOperator_conjugateAdjointSandwich
        U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap ha,
      conjugateAdjointSandwich_apply_symm U V a⟩

end InnerProductSpace
