/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartContinuity
import MathlibAnnex.Analysis.InnerProductSpace.ConjugateAdjoint

/-!
# Bounded vector changes on the actual normal parts

These are the concrete adjoint specializations of the full-continuity
criterion. All operator products have domain and codomain H. In the
conjugate-linear case the adjoint has direction K -> H, so V* b U is linear,
and coefficient values are conjugated. The final two constructions start
with algebraic bijections and forward continuity only: inverse continuity
comes from the Banach open mapping theorem, not an extra hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))

include hS in
/-- Theorem 6.9, full continuity criterion for bounded linear bijections. -/
theorem continuous_normalPartLinearMap_iff (U V : H ≃L[ℂ] K) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U.toLinearEquiv V.toLinearEquiv) ↔
      ∀ b : T, InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap
        (b : K →L[ℂ] K) ∈ S :=
  continuous_normalPartSemilinearMap_iff S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)

/-- Both directions of full continuity, iff V* B U is exactly A. -/
theorem continuous_normalPartLinearMap_and_inverse_iff (U V : H ≃L[ℂ] K) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
        (normalPartSemilinearMap S T hT U.toLinearEquiv V.toLinearEquiv) ∧
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (normalPartSemilinearMap T S hS U.symm.toLinearEquiv V.symm.toLinearEquiv)) ↔
      InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)) :=
  continuous_normalPartSemilinearMap_and_inverse_iff S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (InnerProductSpace.inner_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)

/-- The full homeomorphism on the already constructed kernel equivalence. -/
def normalPartLinearHomeomorph (U V : H ≃L[ℂ] K)
    (heq : InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
      (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartSemilinearHomeomorphOfOperatorImage S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (InnerProductSpace.inner_adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_adjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap) heq

include hS in
/-- The conjugate-linear continuity criterion uses the actual conjugate-linear adjoint. -/
theorem continuous_normalPartConjugateLinearMap_iff
    (U V : H ≃SL[starRingEnd ℂ] K) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U.toLinearEquiv V.toLinearEquiv) ↔
      ∀ b : T, InnerProductSpace.conjugateAdjointSandwich
        U.toContinuousLinearMap V.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S :=
  continuous_normalPartSemilinearMap_iff S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)

/-- The conjugate-linear homeomorphism criterion, with concrete operator-subspace equality. -/
theorem continuous_normalPartConjugateLinearMap_and_inverse_iff
    (U V : H ≃SL[starRingEnd ℂ] K) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
        (normalPartSemilinearMap S T hT U.toLinearEquiv V.toLinearEquiv) ∧
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (normalPartSemilinearMap T S hS U.symm.toLinearEquiv V.symm.toLinearEquiv)) ↔
      InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)) :=
  continuous_normalPartSemilinearMap_and_inverse_iff S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (InnerProductSpace.inner_conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_conjugateAdjointSandwich
      U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)

/-- Actual full homeomorphism in the conjugate-linear case. -/
def normalPartConjugateLinearHomeomorph (U V : H ≃SL[starRingEnd ℂ] K)
    (heq : InnerProductSpace.conjugateAdjointSandwich
      U.toContinuousLinearMap V.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartSemilinearHomeomorphOfOperatorImage S T hS hT (fun _ => rfl)
    U.toLinearEquiv V.toLinearEquiv
    (InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.conjugateAdjointSandwich U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap)
    (InnerProductSpace.inner_conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap)
    (InnerProductSpace.inner_conjugateAdjointSandwich
      U.symm.toContinuousLinearMap V.symm.toContinuousLinearMap) heq

/-- Starting with algebraic linear bijections, only forward continuity is supplied.
The two inverse maps are made continuous by the genuine Banach theorem. -/
def normalPartLinearHomeomorphOfContinuous
    (U V : H ≃ₗ[ℂ] K) (hU : Continuous U) (hV : Continuous V)
    (heq : InnerProductSpace.adjointSandwich
      (U.toContinuousLinearEquivOfContinuous hU).toContinuousLinearMap
      (V.toContinuousLinearEquivOfContinuous hV).toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartLinearHomeomorph S T hS hT
    (U.toContinuousLinearEquivOfContinuous hU) (V.toContinuousLinearEquivOfContinuous hV) heq

/-- The same automatic bounded-inverse connection for algebraic conjugate-linear bijections. -/
def normalPartConjugateLinearHomeomorphOfContinuous
    (U V : H ≃ₛₗ[starRingEnd ℂ] K) (hU : Continuous U) (hV : Continuous V)
    (heq : InnerProductSpace.conjugateAdjointSandwich
      (U.toContinuousLinearEquivOfContinuous hU).toContinuousLinearMap
      (V.toContinuousLinearEquivOfContinuous hV).toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartConjugateLinearHomeomorph S T hS hT
    (U.toContinuousLinearEquivOfContinuous hU) (V.toContinuousLinearEquivOfContinuous hV) heq

include hS in
/-- The continuity criterion with algebraic linear bijections as input.
Only forward continuity is assumed; the inverse is supplied by the Banach theorem. -/
theorem continuous_normalPartLinearMap_iff_of_continuous
    (U V : H ≃ₗ[ℂ] K) (hU : Continuous U) (hV : Continuous V) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U V) ↔
      ∀ b : T, InnerProductSpace.adjointSandwich
        (U.toContinuousLinearEquivOfContinuous hU).toContinuousLinearMap
        (V.toContinuousLinearEquivOfContinuous hV).toContinuousLinearMap
        (b : K →L[ℂ] K) ∈ S :=
  continuous_normalPartLinearMap_iff S T hS hT
    (U.toContinuousLinearEquivOfContinuous hU) (V.toContinuousLinearEquivOfContinuous hV)

include hS in
/-- The same criterion for algebraic conjugate-linear bijections with forward continuity. -/
theorem continuous_normalPartConjugateLinearMap_iff_of_continuous
    (U V : H ≃ₛₗ[starRingEnd ℂ] K) (hU : Continuous U) (hV : Continuous V) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U V) ↔
      ∀ b : T, InnerProductSpace.conjugateAdjointSandwich
        (U.toContinuousLinearEquivOfContinuous hU).toContinuousLinearMap
        (V.toContinuousLinearEquivOfContinuous hV).toContinuousLinearMap
        (b : K →L[ℂ] K) ∈ S :=
  continuous_normalPartConjugateLinearMap_iff S T hS hT
    (U.toContinuousLinearEquivOfContinuous hU) (V.toContinuousLinearEquivOfContinuous hV)

end MathlibAnnex.Analysis.CStarAlgebra
