/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.InternalTypeI

set_option autoImplicit false
noncomputable section
open MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (hA : IsInternalTypeI A) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) : ∃ a : A, pi a ≠ 0 ∧ IsCompactOperator (pi a) :=
  IsInternalTypeI.exists_nonzero_compact_image (A := A) (H := H) hA pi hpi

example (hA : IsInternalTypeI A) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi :=
  IsInternalTypeI.compact_le_range (A := A) (H := H) hA pi hpi

example (hA : IsInternalTypeI A) : IsGCR A := IsInternalTypeI.isGCR (A := A) hA

example : IsGCR A ↔ ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
    ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)) :=
  isGCR_iff_component_compact_comparison (A := A)

example (hA : IsInternalTypeI A) (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)) :=
  IsInternalTypeI.component_compact_comparison (A := A) hA I
