/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartCompactComparison
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartFiniteConjugation

/-!
# Representation-side GCR and CCR criteria from actual components

No independent factor-representation definition of type I or Glimm--Sakai
bridge is assumed here. The left sides of the criteria are explicitly the
compact containment/equality conditions on actual irreducible images. The
right sides are separately named geometric comparison predicates, NOT
renamings or definitions of type I.

The small tests use Hilbert carriers in the algebra universe, where the actual
pure GNS witnesses live. Separate theorems transport the conclusion to EVERY
independently specified Hilbert universe through an actual unitary equivalence.
No universe of all Hilbert spaces is formed. A model Hilbert space is explicitly
nontrivial; a merely subsingleton empty spectrum is not a compact target model.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace ClosureSpace

open MathlibAnnex.Analysis.CStarAlgebra
attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

/-- The geometric conclusion in the continuous finite comparison criterion.
This predicate says nothing by definition about irreducible representation images. -/
def HasContinuousFiniteCompactComparison.{uH, uX} {X : Type uX}
    (c : ClosureSpace X) : Prop :=
  ∃ (H : Type uH) (instN : NormedAddCommGroup H),
    letI := instN
    ∃ instI : InnerProductSpace ℂ H,
      letI := instI
      ∃ instC : CompleteSpace H,
        letI := instC
        ∃ instT : Nontrivial H,
          letI := instT
          ∃ e : FiniteHomeomorph c
              (NormedSpace.geometricStructureClosure ℂ
                (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)),
            c.Continuous (NormedSpace.geometricStructureClosure ℂ
              (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) e.toEquiv

/-- The full-homeomorphism conclusion, kept separate from the one-direction
continuity predicate. -/
def HasCompactOperatorHomeomorph.{uH, uX} {X : Type uX}
    (c : ClosureSpace X) : Prop :=
  ∃ (H : Type uH) (instN : NormedAddCommGroup H),
    letI := instN
    ∃ instI : InnerProductSpace ℂ H,
      letI := instI
      ∃ instC : CompleteSpace H,
        letI := instC
        ∃ instT : Nontrivial H,
          letI := instT
          Nonempty (Homeomorph c
            (NormedSpace.geometricStructureClosure ℂ
              (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)))

end ClosureSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra
  HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

section Concrete
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

include hS in
/-- The concrete equivalence. The forward witness is H itself; the converse
accepts any witnessed nonzero model in this universe and uses the actual map. -/
theorem compact_le_iff_normalPart_hasContinuousFiniteCompactComparison :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S ↔
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) := by
  constructor
  · intro h
    letI : Nontrivial H :=
      NonUnitalCStarRepresentation.nontrivial_of_isNonzero
        (NonUnitalStarSubalgebraClass.subtype S) hS.1
    exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
      normalPartToCompactFiniteHomeomorph S hS,
      continuous_normalPartToCompactFiniteHomeomorph S hS h⟩
  · rintro ⟨K, instN, instI, instC, instT, e, he⟩
    letI := instN
    letI := instI
    letI := instC
    letI := instT
    exact compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph S hS e he

include hS in
/-- The concrete CCR counterpart uses full homeomorphisms on the right. -/
theorem eq_compact_iff_normalPart_hasCompactOperatorHomeomorph :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ↔
      ClosureSpace.HasCompactOperatorHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) := by
  constructor
  · intro h
    letI : Nontrivial H :=
      NonUnitalCStarRepresentation.nontrivial_of_isNonzero
        (NonUnitalStarSubalgebraClass.subtype S) hS.1
    exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
      nonempty_homeomorph_compact_of_eq S h⟩
  · rintro ⟨K, instN, instI, instC, instT, ⟨e⟩⟩
    letI := instN
    letI := instI
    letI := instC
    letI := instT
    exact eq_compactOperatorStarSubalgebra_of_homeomorph S hS e

end Concrete

section Algebra
variable {A : Type u} [NonUnitalCStarAlgebra A] [hA : Nontrivial A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pure GNS tests imply compact containment for any irreducible representation
in an independently specified Hilbert universe. The bridge is a real unitary
intertwiner, not equality of primitive kernels. -/
theorem compact_le_range_of_forall_pure_state
    (h : ∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤ (NonUnitalStarAlgHom.range phi.gnsRepresentation))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi) := by
  obtain ⟨phi, hU⟩ := pi.exists_pureState_unitaryEquivalent_gnsRepresentation hpi
  exact hU.symm.compactOperatorStarSubalgebra_le_range (h phi)

/-- The same actual unitary transports the full compact-image equality. -/
theorem range_eq_compact_of_forall_pure_state
    (h : ∀ phi : NonUnitalPureState A,
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  obtain ⟨phi, hU⟩ := pi.exists_pureState_unitaryEquivalent_gnsRepresentation hpi
  exact hU.symm.range_eq_compactOperatorStarSubalgebra (h phi)

include hA in
/-- A compact target may initially inhabit ANY specified universe. Composing
its actual comparison with the GNS normal-part restriction proves the small
pure-GNS condition. No downward ULift or assumed smallness is used. -/
theorem forall_pure_state_compact_le_of_component_compact_comparisons
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I))) :
    ∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤ (NonUnitalStarAlgHom.range phi.gnsRepresentation) := by
  intro phi
  let pi := phi.gnsRepresentation
  let x := phi.gnsVector
  let I := NonUnitalCStarRepresentation.matrixCoefficientKernel pi
    phi.isIrreducible_gnsRepresentation x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  let a := imageNormalPartHomeomorph pi phi.isIrreducible_gnsRepresentation
    x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  obtain ⟨K, instN, instI, instC, instT, e, he⟩ := h I
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  exact compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph (NonUnitalStarAlgHom.range pi)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2
      phi.isIrreducible_gnsRepresentation)
    (a.toFiniteHomeomorph.trans e) (he.comp a.continuous_toFun)


include hA in
/-- Representation-side GCR, expressed first with actual small pure GNS tests.
Each component model is composed from the existing literal preimage normal-part
homeomorphism and the identity-vector compact comparison. -/
theorem forall_pure_state_compact_le_iff_component_compact_comparison :
    (∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤ (NonUnitalStarAlgHom.range phi.gnsRepresentation)) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) := by
  constructor
  · intro h I
    obtain ⟨K, instN, instI, instC, pi, hpi, a, _ha⟩ :=
      exists_representation_normalPart_homeomorph_component A I
    letI := instN
    letI := instI
    letI := instC
    letI : Nontrivial K := pi.nontrivial_of_isNonzero hpi.1
    have hi := (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi
    let b := normalPartToCompactFiniteHomeomorph (NonUnitalStarAlgHom.range pi) hi
    have hb := continuous_normalPartToCompactFiniteHomeomorph (NonUnitalStarAlgHom.range pi) hi
      (compact_le_range_of_forall_pure_state h pi hpi)
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      a.symm.toFiniteHomeomorph.trans b, hb.comp a.continuous_invFun⟩
  · exact forall_pure_state_compact_le_of_component_compact_comparisons

include hA in
/-- The component criterion implies compact containment for ALL independently
specified Hilbert universes, not just the small GNS representatives. -/
theorem compact_le_range_of_component_compact_comparisons
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi) :=
  compact_le_range_of_forall_pure_state
    (forall_pure_state_compact_le_of_component_compact_comparisons h) pi hpi

include hA in
/-- Exact all-representation form with the small universe explicitly fixed.
The preceding theorem is the independently quantified extension to any other
Hilbert universe. No independent type-I equivalence is asserted. -/
theorem forall_irreducible_compact_le_iff_component_compact_comparison :
    (∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
      ∀ pi : NonUnitalCStarRepresentation A K, pi.IsIrreducible →
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ (NonUnitalStarAlgHom.range pi)) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasContinuousFiniteCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) := by
  constructor
  · intro h
    apply forall_pure_state_compact_le_iff_component_compact_comparison.1
    intro phi
    exact h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  · intro h K _ _ _ pi hpi
    exact compact_le_range_of_component_compact_comparisons h pi hpi

include hA in
/-- Arbitrary-universe FULL compact component models yield the actual compact
image equality in the small pure GNS representatives. -/
theorem forall_pure_state_range_eq_compact_of_component_compact_homeomorphs
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasCompactOperatorHomeomorph.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I))) :
    ∀ phi : NonUnitalPureState A,
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS := by
  intro phi
  let pi := phi.gnsRepresentation
  let x := phi.gnsVector
  let I := NonUnitalCStarRepresentation.matrixCoefficientKernel pi
    phi.isIrreducible_gnsRepresentation x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  let a := imageNormalPartHomeomorph pi phi.isIrreducible_gnsRepresentation
    x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  obtain ⟨K, instN, instI, instC, instT, ⟨e⟩⟩ := h I
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  exact eq_compactOperatorStarSubalgebra_of_homeomorph (NonUnitalStarAlgHom.range pi)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2
      phi.isIrreducible_gnsRepresentation)
    (a.trans e)


include hA in
/-- The CCR counterpart: actual compact-image equality corresponds to FULL
component homeomorphisms, rather than merely continuous finite homeomorphisms. -/
theorem forall_pure_state_range_eq_compact_iff_component_compact_homeomorph :
    (∀ phi : NonUnitalPureState A,
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasCompactOperatorHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) := by
  constructor
  · intro h I
    obtain ⟨K, instN, instI, instC, pi, hpi, a, _ha⟩ :=
      exists_representation_normalPart_homeomorph_component A I
    letI := instN
    letI := instI
    letI := instC
    letI : Nontrivial K := pi.nontrivial_of_isNonzero hpi.1
    obtain ⟨b⟩ := nonempty_homeomorph_compact_of_eq (NonUnitalStarAlgHom.range pi)
      (range_eq_compact_of_forall_pure_state h pi hpi)
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ⟨a.symm.trans b⟩⟩
  · exact forall_pure_state_range_eq_compact_of_component_compact_homeomorphs

include hA in
/-- Full component comparison implies compact-image equality in every separate
Hilbert universe, through actual unitary transport. -/
theorem range_eq_compact_of_component_compact_homeomorphs
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasCompactOperatorHomeomorph.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
  range_eq_compact_of_forall_pure_state
    (forall_pure_state_range_eq_compact_of_component_compact_homeomorphs h) pi hpi

include hA in
/-- Exact all-representation CCR criterion, with small representatives and
arbitrary-Hilbert-universe transport separately proved. -/
theorem forall_irreducible_range_eq_compact_iff_component_compact_homeomorph :
    (∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
      ∀ pi : NonUnitalCStarRepresentation A K, pi.IsIrreducible →
        (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasCompactOperatorHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) := by
  constructor
  · intro h
    apply forall_pure_state_range_eq_compact_iff_component_compact_homeomorph.1
    intro phi
    exact h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  · intro h K _ _ _ pi hpi
    exact range_eq_compact_of_component_compact_homeomorphs h pi hpi

end Algebra
end MathlibAnnex.Analysis.CStarAlgebra
