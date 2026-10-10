/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.GCRCharacterization
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralPreserver
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactlyRepresented
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PrimitiveCompactRange
import MathlibAnnex.Analysis.CStarAlgebra.Representation.DiscreteCCRCompact
import MathlibAnnex.Topology.ClosureSpace.ComponentSubspace

/-!
# Transport of compact representability by a full geometric-structure homeomorphism

A specified faithful compact-valued representation of `A` supplies actual
compact models for every geometric component of `A`. Restriction of the
inverse of the given full closure homeomorphism transports those models to
components of `B`. The model Hilbert universe remains that of `A`; the
arbitrary-universe component criterion, not a small-universe iff for `B`,
then gives compact ranges for the pure GNS representations of `B`.

The actual ordinary primitive-spectrum homeomorphism transports discreteness.
The target is the already defined `PrimitiveSpectrum.reducedAtomicRepresentation`,
not a newly chosen representation. Its compactness and its literal c₀ diagonal
range follow from the received discrete CCR converse. In particular, neither
CCR nor discreteness nor compact representability of `B` is an input.

Nontriviality is obtained only when an actual geometric or primitive point is
being used. A geometric point is impossible in a subsingleton algebra; an
actual primitive point supplies a nonzero irreducible GNS action. Thus the
empty-spectrum and zero-algebra cases are not excluded by public hypotheses.
The canonical spectral orders are local and no auxiliary order is exported.

Existence invariance is stated with a Hilbert witness in each algebra's own
universe. The pointwise transport starts with a representation on any separate
Hilbert universe and lands on the canonical target Hilbert space. This does
not assert compactness of an arbitrary preassigned target representation, nor
surjectivity onto all compact operators on the target Hilbert direct sum.
No assertion about a star isomorphism inducing the specified geometric map is
made here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set
open scoped Classical CStarAlgebra ENNReal lp Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w z

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type z} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The zero branch is discharged from the actual point, rather than by
adding nontriviality to all subsequent statements. -/
private theorem nontrivial_of_geometricStructureSpace
    (I : NormedSpace.GeometricStructureSpace ℂ A) : Nontrivial A := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hA
  letI : Subsingleton A := hA
  letI : IsEmpty (NormedSpace.GeometricStructureSpace ℂ A) :=
    NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ A
  exact isEmptyElim I

/-- A full geometric homeomorphism transfers each actual compact component
model. The witness Hilbert space stays in universe `u`, independently of the
universe `v` of `B` and the universe `w` of the given faithful action. -/
theorem hasCompactOperatorHomeomorph_component_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (I : NormedSpace.GeometricStructureSpace ℂ B) :
    ClosureSpace.HasCompactOperatorHomeomorph.{u, v}
      ((NormedSpace.geometricStructureClosure ℂ B).subspace
        ((NormedSpace.geometricStructureClosure ℂ B).component I)) := by
  letI : Nontrivial A := nontrivial_of_geometricStructureSpace (e.toEquiv.symm I)
  have hPure : ∀ phi : NonUnitalPureState A,
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS :=
    NonUnitalCStarRepresentation.range_gnsRepresentation_eq_compact_of_isCompactlyRepresented
      pi hpi
  have hModel :=
    (forall_pure_state_range_eq_compact_iff_component_compact_homeomorph
      (A := A)).1 hPure (e.toEquiv.symm I)
  obtain ⟨L, instN, instI, instC, instT, ⟨f⟩⟩ := hModel
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(e.symm.component I).trans f⟩⟩

namespace PrimitiveSpectrum

/-- The selected target GNS compact-range equality is derived, not assumed.
Only at this actual primitive point is nontriviality of `B` introduced. The
component models may live in `A`'s universe, so the arbitrary-model-universe
criterion is used before the received selected/pure-GNS bridge. -/
theorem range_pureStateRepresentative_eq_compact_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (P : PrimitiveSpectrum B) :
    (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS := by
  letI : Nontrivial B :=
    NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero
      P.pureStateRepresentative.gnsRepresentation
      P.pureStateRepresentative.isIrreducible_gnsRepresentation.1
  have hPure : ∀ phi : NonUnitalPureState B,
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS :=
    forall_pure_state_range_eq_compact_of_component_compact_homeomorphs
      (hasCompactOperatorHomeomorph_component_of_geometricStructure_homeomorph e pi hpi)
  exact
    (forall_pureState_range_eq_compact_iff_forall_pureStateRepresentative_range_eq_compact
      (A := B)).1 hPure P

end PrimitiveSpectrum

namespace NonUnitalCStarRepresentation

/-- CCR for a target irreducible action on any independently specified
Hilbert universe. The shared primitive compact-range provider constructs the
actual unitary lift; no equal-kernel-only inference or duplicate lift is used. -/
theorem range_eq_compactOperatorStarSubalgebra_of_isIrreducible_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (rho : NonUnitalCStarRepresentation B K) (hrho : rho.IsIrreducible) :
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K :=
  range_eq_compact_of_forall_pureStateRepresentative_range_eq_compact
    (PrimitiveSpectrum.range_pureStateRepresentative_eq_compact_of_geometricStructure_homeomorph
      e pi hpi) rho hrho

end NonUnitalCStarRepresentation

/-- Discreteness is transported through the actual ordinary primitive-spectrum
homeomorphism. Each target singleton supplies the local nontrivial instances
required by that provider. If the target spectrum is empty, the singleton
criterion is vacuous; if `A` is zero, its inverse coefficient point is impossible. -/
theorem discreteTopology_primitiveSpectrum_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    DiscreteTopology (PrimitiveSpectrum B) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro P
  let phi := P.pureStateRepresentative
  letI : Nontrivial B :=
    NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation.1
  let I : NormedSpace.GeometricStructureSpace ℂ B :=
    NonUnitalCStarRepresentation.matrixCoefficientKernel phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
      phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  letI : Nontrivial A := nontrivial_of_geometricStructureSpace (e.toEquiv.symm I)
  letI : DiscreteTopology (PrimitiveSpectrum A) :=
    discreteTopology_primitiveSpectrum_of_isCompactlyRepresented pi hpi
  let f : PrimitiveSpectrum A ≃ₜ PrimitiveSpectrum B :=
    primitiveSpectrumHomeomorphOfGeometricStructure e
  have hopen : IsOpen (f.symm ⁻¹'
      ({f.symm P} : Set (PrimitiveSpectrum A))) :=
    (isOpen_discrete _).preimage f.symm.continuous
  have heq : f.symm ⁻¹' ({f.symm P} : Set (PrimitiveSpectrum A)) = {P} := by
    ext Q
    change f.symm Q = f.symm P ↔ Q = P
    exact f.symm.injective.eq_iff
  rw [heq] at hopen
  exact hopen

namespace PrimitiveSpectrum

/-- The same canonical reduced atomic representation of `B` is faithfully
compact. Both input conditions of the received converse are proved above. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (reducedAtomicRepresentation (A := B)).IsCompactlyRepresented := by
  letI : DiscreteTopology (PrimitiveSpectrum B) :=
    discreteTopology_primitiveSpectrum_of_geometricStructure_homeomorph e pi hpi
  exact isCompactlyRepresented_reducedAtomicRepresentation
    (range_pureStateRepresentative_eq_compact_of_geometricStructure_homeomorph e pi hpi)

/-- Each value of that very reduced atomic map is compact. Its already proved
injectivity, norm equality, coordinate action and adjoint formula are unchanged. -/
theorem isCompactOperator_reducedAtomicRepresentation_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (b : B) : IsCompactOperator (reducedAtomicRepresentation (A := B) b) :=
  (isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
    e pi hpi).2 b

/-- The literal target range is the c₀ block-diagonal range on its genuine
Hilbert sum. No surjectivity onto all compact operators is asserted. -/
theorem range_reducedAtomicRepresentation_eq_range_diagonalRepresentation_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := B))) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum B => P.pureStateRepresentative.GNS))) := by
  letI : DiscreteTopology (PrimitiveSpectrum B) :=
    discreteTopology_primitiveSpectrum_of_geometricStructure_homeomorph e pi hpi
  exact reducedAtomicRepresentation_range_eq_c0_diagonalRepresentation_range
    (range_pureStateRepresentative_eq_compact_of_geometricStructure_homeomorph e pi hpi)

/-- The equivalent compact intersection uses the existing bounded product
range, not the entire ambient operator algebra as the diagonal range. -/
theorem range_reducedAtomicRepresentation_eq_range_diagonalRepresentation_inf_compactOperatorStarSubalgebra_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := B))) =
      (NonUnitalStarAlgHom.range (CompactOperatorBoundedProduct.diagonalRepresentation
        (fun P : PrimitiveSpectrum B => P.pureStateRepresentative.GNS))) ⊓
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (ReducedAtomicHilbertSpace B) := by
  letI : DiscreteTopology (PrimitiveSpectrum B) :=
    discreteTopology_primitiveSpectrum_of_geometricStructure_homeomorph e pi hpi
  exact reducedAtomicRepresentation_range_eq_bounded_diagonalRepresentation_range_inf_compactOperatorStarSubalgebra
    (range_pureStateRepresentative_eq_compact_of_geometricStructure_homeomorph e pi hpi)

/-- Invariance for the two already named canonical representations. Reversal
uses the same transport with `e.symm`, not compactness of arbitrary chosen actions. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_iff_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented ↔
      (reducedAtomicRepresentation (A := B)).IsCompactlyRepresented := by
  constructor
  · intro hA
    exact isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
      e (reducedAtomicRepresentation (A := A)) hA
  · intro hB
    exact isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
      e.symm (reducedAtomicRepresentation (A := B)) hB

end PrimitiveSpectrum

/-- Existence of a faithful compact-valued representation is a full GSS
invariant. Each side uses a Hilbert witness in its own algebra universe. The
forward construction above separately accepts a given source action on ANY
Hilbert universe, and returns the canonical target action without a new choice. -/
theorem exists_isCompactlyRepresented_iff_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    (∃ (L : Type u) (instN : NormedAddCommGroup L),
      letI := instN
      ∃ instI : InnerProductSpace ℂ L,
        letI := instI
        ∃ instC : CompleteSpace L,
          letI := instC
          ∃ pi : NonUnitalCStarRepresentation A L, pi.IsCompactlyRepresented) ↔
    (∃ (L : Type v) (instN : NormedAddCommGroup L),
      letI := instN
      ∃ instI : InnerProductSpace ℂ L,
        letI := instI
        ∃ instC : CompleteSpace L,
          letI := instC
          ∃ pi : NonUnitalCStarRepresentation B L, pi.IsCompactlyRepresented) := by
  constructor
  · rintro ⟨L, instN, instI, instC, pi, hpi⟩
    letI := instN
    letI := instI
    letI := instC
    exact ⟨PrimitiveSpectrum.ReducedAtomicHilbertSpace B,
      inferInstance, inferInstance, inferInstance,
      PrimitiveSpectrum.reducedAtomicRepresentation (A := B),
      PrimitiveSpectrum.isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
        e pi hpi⟩
  · rintro ⟨L, instN, instI, instC, pi, hpi⟩
    letI := instN
    letI := instI
    letI := instC
    exact ⟨PrimitiveSpectrum.ReducedAtomicHilbertSpace A,
      inferInstance, inferInstance, inferInstance,
      PrimitiveSpectrum.reducedAtomicRepresentation (A := A),
      PrimitiveSpectrum.isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
        e.symm pi hpi⟩

end MathlibAnnex.Analysis.CStarAlgebra
