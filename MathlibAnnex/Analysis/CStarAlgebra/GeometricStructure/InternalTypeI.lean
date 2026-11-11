/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRCharacterization
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRConverse
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.GCRCharacterization

/-!
# The component consequence of internal type I

The existing component theorem is reused for the representation-side GCR
condition. The zero algebra is handled by the existing emptiness theorem.
The forward implication keeps the quotient and rank-one proof. The converse
uses the independently constructed CAR subquotient and GCR permanence; no
bidual classification or final equivalence from another lane is used.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The named GCR predicate has exactly the established component meaning,
including the zero algebra. The model universe equals the algebra universe. -/
theorem isGCR_iff_component_compact_comparison :
    IsGCR A ↔ ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    letI := NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ A
    constructor
    · intro _ I
      exact isEmptyElim I
    · intro _
      exact isGCR_of_subsingleton
  · letI := hA
    exact forall_pure_state_compact_le_iff_component_compact_comparison

/-- The internal quotient condition supplies the actual continuous finite
compact comparison for each existing geometric component. -/
theorem IsInternalTypeI.component_compact_comparison (hA : IsInternalTypeI A)
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)) :=
  isGCR_iff_component_compact_comparison.mp hA.isGCR I

/-- The independent internal type I condition has exactly the established
GSS component meaning, with the zero algebra and nonunital algebras included. -/
theorem isInternalTypeI_iff_component_compact_comparison :
    IsInternalTypeI A ↔ ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) :=
  isInternalTypeI_iff_isGCR.trans isGCR_iff_component_compact_comparison

end MathlibAnnex.Analysis.CStarAlgebra
