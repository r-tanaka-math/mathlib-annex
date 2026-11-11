/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRConverse
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.InternalTypeI

noncomputable section
set_option autoImplicit false

open Set
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

-- No ambient unit, separability, nonzero projection, or other-lane equivalence.
example (hA : IsGCR A) : IsInternalTypeI A := hA.isInternalTypeI

example : IsInternalTypeI A ↔ IsGCR A := isInternalTypeI_iff_isGCR

example :
    (∀ (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)), J ≠ ⊤ →
      ∃ a : ClosedIdealQuotient.Quotient J hJ, a ≠ 0 ∧ IsAbelianPositiveElement a) ↔
    (∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
        NonUnitalStarAlgHom.range phi.gnsRepresentation) :=
  isInternalTypeI_iff_isGCR (A := A)

example [Subsingleton A] : IsInternalTypeI A :=
  isGCR_of_subsingleton.isInternalTypeI

example (hA : IsGCR A) (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    IsInternalTypeI (ClosedIdealQuotient.Quotient J hJ) :=
  (hA.closed_ideal_quotient J hJ).isInternalTypeI

example [Nontrivial A] (hA : IsAntiliminal A) : ¬ IsGCR A := hA.not_isGCR

example (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
    ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I))) : IsInternalTypeI A :=
  isInternalTypeI_iff_component_compact_comparison.mpr h

example (hA : IsInternalTypeI A) :
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) :=
  isInternalTypeI_iff_component_compact_comparison.mp hA
