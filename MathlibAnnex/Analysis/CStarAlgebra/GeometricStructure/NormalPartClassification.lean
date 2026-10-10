/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinearBounded
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartLinearClassification

/-!
# Analytic classification for the already selected normal-part factors

This is the concrete application of the regular-pair classification, not another
regularity theorem. Infinite dimensionality is assumed only for the source;
both rank bounds and the regularity of the SAME selected factors are derived.
The specified finite homeomorphism supplies the global orientation. All
hypotheses used only by proofs are explicit theorem arguments. No inverse full
continuity is assumed for inclusion, and the conditional equality is separated
below into an additional theorem with that hypothesis.

The Hilbert-basis cardinality conclusion of the paper is not asserted here.
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
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

/-- Forward full continuity classifies the SAME selected pair. The continuous
bundles agree with both original functions and both original inverse functions.
Their common scalar type, the equality with the specified normal-part map, and
operator inclusion are conclusions. Operator equality is only conditional on
full continuity of the original inverse. No pair is reselected on projective rays. -/
theorem exists_normalPart_selected_operator_inclusion
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd ∧
    ((∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ b : T, InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm →
        InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)))) ∨
    (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ b : T, InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm →
        InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))))) := by
  dsimp only
  let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
  have hK : 2 ≤ Module.rank ℂ K :=
    (show (2 : Cardinal.{v}) ≤ 3 by norm_num).trans
      (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).2
  have hs := normalPart_semilinear_factors_scalar_types S T hS hT e hd hH hcont
  have hc := normalPart_semilinear_factors_continuous S T hS hT e hd hH hcont
  apply exists_same_type_normalPart_operator_inclusion S T hS hT
    (normalPartFirstSemilinearEquiv S T hS hT e hd)
    (normalPartSecondSemilinearEquiv S T hS hT e hd)
    hs.1 hs.2 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 e.toEquiv hK hcont
  rcases normalPart_semilinear_factors_evaluation S T hS hT e hd with
    ⟨hforward, _⟩ | ⟨hforward, _⟩
  · exact Or.inl hforward
  · exact Or.inr hforward

/-- The equality of the selected scalar automorphisms follows from the actual
classification, not merely from their individual identity/conjugation alternatives. -/
theorem normalPart_selected_scalar_eq
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd :=
  (exists_normalPart_selected_operator_inclusion S T hS hT e hH hcont).1

/-- Only the two same-type alternatives remain for the selected pair. In
particular, the two mixed cases are eliminated rather than silently omitted. -/
theorem normalPart_selected_scalar_types
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    (normalPartFirstScalarEquiv S T hS hT e hd = RingEquiv.refl ℂ ∧
      normalPartSecondScalarEquiv S T hS hT e hd = RingEquiv.refl ℂ) ∨
    (normalPartFirstScalarEquiv S T hS hT e hd = starRingAut (R := ℂ) ∧
      normalPartSecondScalarEquiv S T hS hT e hd = starRingAut (R := ℂ)) := by
  dsimp only
  let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
  have hsame := normalPart_selected_scalar_eq S T hS hT e hH hcont
  rcases (normalPart_semilinear_factors_scalar_types S T hS hT e hd hH hcont).1 with
    hlin | hconj
  · exact Or.inl ⟨hlin, hsame.symm.trans hlin⟩
  · exact Or.inr ⟨hconj, hsame.symm.trans hconj⟩

/-- With full continuity in BOTH directions, the same functions and inverses
realize equality of the operator subspaces. The extra hypothesis is not required
for, and must not be inferred from, the preceding inclusion theorem. -/
theorem exists_normalPart_selected_operator_eq
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (hcontInv : ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd ∧
    (
    (∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) ∨
    (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)))) := by
  dsimp only
  obtain ⟨hsame, hpair⟩ :=
    exists_normalPart_selected_operator_inclusion S T hS hT e hH hcont
  refine ⟨hsame, ?_⟩
  rcases hpair with ⟨Uc, Vc, hU, hV, hUi, hVi, heq, _, hEq⟩ |
    ⟨Uc, Vc, hU, hV, hUi, hVi, heq, _, hEq⟩
  · exact Or.inl ⟨Uc, Vc, hU, hV, hUi, hVi, heq, hEq hcontInv⟩
  · exact Or.inr ⟨Uc, Vc, hU, hV, hUi, hVi, heq, hEq hcontInv⟩

end MathlibAnnex.Analysis.CStarAlgebra
