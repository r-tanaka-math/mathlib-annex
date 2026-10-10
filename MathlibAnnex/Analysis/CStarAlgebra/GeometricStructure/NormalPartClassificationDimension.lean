/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClassificationConsequences
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartHilbertDimension

/-!
# Binding selected normal-part lifts to genuine Hilbert dimension

This small binding combines the actual selected-pair classification and the
actual normal-part HilbertBasis theorem for the SAME `e` and forward continuity.
It retains both selected functions and both inverse functions. The complete
point, literal-kernel, global direct/swap and sandwich conclusions remain in
`exists_normalPart_selected_classification` and its `_eq` version, rather than
being copied into a second several-hundred-line statement.

Use this theorem together with those two existing declarations. The `_eq`
declaration additionally requires full inverse continuity. The finite-dimensional
comparison and the rank-three algebraic realization retain their weaker original
assumptions in their own modules. The selected lifts are not asserted isometric.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Cardinal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uI uJ
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type uI} {κ : Type uJ}
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

/-- Compact joint endpoint: the same selected pair has one common linear or
conjugate-linear type, with the same inverse functions, and arbitrary Hilbert
bases have equinumerous indices after lifting universes. The strong classification
used in the proof still supplies all point/kernel/inclusion formulas. -/
theorem exists_normalPart_selected_pair_and_hilbertBasis_lift_mk_eq
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) ∧
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd ∧
    ((∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z)) ∨
     (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z))) := by
  dsimp only
  obtain ⟨hsame, hpair⟩ := exists_normalPart_selected_classification S T hS hT e hH hcont
  refine ⟨hilbertBasis_lift_mk_eq_of_normalPart_continuous S T hS hT e hcont b c,
    hsame, ?_⟩
  rcases hpair with ⟨Uc, Vc, hU, hV, hUi, hVi, hrest⟩ |
    ⟨Uc, Vc, hU, hV, hUi, hVi, hrest⟩
  · exact Or.inl ⟨Uc, Vc, hU, hV, hUi, hVi⟩
  · exact Or.inr ⟨Uc, Vc, hU, hV, hUi, hVi⟩

end MathlibAnnex.Analysis.CStarAlgebra
