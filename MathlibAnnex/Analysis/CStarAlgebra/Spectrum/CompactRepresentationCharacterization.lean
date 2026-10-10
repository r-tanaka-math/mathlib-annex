/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactlyRepresented
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PrimitiveCompactRange
import MathlibAnnex.Analysis.CStarAlgebra.Representation.DiscreteCCRCompact

/-!
# Characterization of algebras admitting faithful compact representations

A nonunital complex C-star algebra admits a faithful compact-valued
representation if and only if its primitive spectrum is discrete and every
nonzero irreducible representation has literal range equal to the compact
operators. The intrinsic representative used here is the already defined
`PrimitiveSpectrum.reducedAtomicRepresentation`, not a second chosen map.

The quantified test in the equivalences uses Hilbert spaces in `Type u`,
where the algebra lies in `Type u`. This universe contains the selected GNS
spaces and their dependent Hilbert sum. The common primitive-range bridge
lifts the conclusion to any independently specified Hilbert universe.
Conversely, the first theorem starts from an actual compact representation
in an independent `Type v` and proves compactness of this same reduced atomic
map. No universe-shrinking equivalence or `ULift` identification is assumed.

The existential formulas expose each Hilbert-space structure before using
it as a local instance. Their reverse witness is the existing reduced atomic
Hilbert sum with its existing structures and representation. No new CCR
predicate, representation definition, or choice operation is introduced.

The algebraic condition does not say that an arbitrary given faithful
representation is compact-valued: infinite multiplicities need not preserve
compactness. The left sides below concern existence or the fixed reduced
atomic representation. The moreover theorem concerns that same map, whose
range is block-diagonal, not all compact operators on the Hilbert sum.

The canonical spectral order is installed only locally. Zero algebras and
empty primitive spectra remain included; no unit, nontriviality, separability,
countability, finite-dimensionality, density, or fiber-model hypothesis is
added to the final characterization.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set
open scoped Classical CStarAlgebra ENNReal lp

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PrimitiveSpectrum

/-- Any actual faithful compact representation, in an independent Hilbert
universe, makes the existing canonical reduced atomic representation
faithfully compact. The latter map is not replaced by the given map. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented := by
  letI : DiscreteTopology (PrimitiveSpectrum A) :=
    discreteTopology_primitiveSpectrum_of_isCompactlyRepresented pi hpi
  exact isCompactlyRepresented_reducedAtomicRepresentation
    (range_pureStateRepresentative_eq_compact_of_isCompactlyRepresented pi hpi)

/-- Intrinsic compact-representation characterization. The all-irreducible
test is in the algebra's universe; the common selected-representative bridge
provides the pointwise conclusion in every independent Hilbert universe. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_iff :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented ↔
      (∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
        rho.IsIrreducible →
          (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) ∧
      DiscreteTopology (PrimitiveSpectrum A) := by
  constructor
  · intro hAtomic
    refine ⟨?_, discreteTopology_primitiveSpectrum_of_isCompactlyRepresented
      (reducedAtomicRepresentation (A := A)) hAtomic⟩
    exact
      (forall_pureStateRepresentative_range_eq_compact_iff_forall_irreducible_range_eq_compact
        (A := A)).mp
        (range_pureStateRepresentative_eq_compact_of_isCompactlyRepresented
          (reducedAtomicRepresentation (A := A)) hAtomic)
  · rintro ⟨hCCR, hDiscrete⟩
    letI : DiscreteTopology (PrimitiveSpectrum A) := hDiscrete
    exact isCompactlyRepresented_reducedAtomicRepresentation
      ((forall_pureStateRepresentative_range_eq_compact_iff_forall_irreducible_range_eq_compact
        (A := A)).mpr hCCR)

end PrimitiveSpectrum

namespace NonUnitalCStarRepresentation

/-- Existence of a faithful compact representation in the algebra's universe
is equivalent to compactness of its fixed reduced atomic representation.
The reverse direction supplies its actual Hilbert space, structures, and
map, rather than choosing an unspecified representation. -/
theorem exists_isCompactlyRepresented_iff_reducedAtomicRepresentation :
    (∃ (K : Type u) (normed : NormedAddCommGroup K),
      letI : NormedAddCommGroup K := normed
      ∃ inner : InnerProductSpace ℂ K,
        letI : InnerProductSpace ℂ K := inner
        ∃ complete : CompleteSpace K,
          letI : CompleteSpace K := complete
          ∃ pi : NonUnitalCStarRepresentation A K, pi.IsCompactlyRepresented) ↔
    (PrimitiveSpectrum.reducedAtomicRepresentation (A := A)).IsCompactlyRepresented := by
  constructor
  · rintro ⟨K, normed, h⟩
    letI : NormedAddCommGroup K := normed
    rcases h with ⟨inner, h⟩
    letI : InnerProductSpace ℂ K := inner
    rcases h with ⟨complete, h⟩
    letI : CompleteSpace K := complete
    rcases h with ⟨pi, hpi⟩
    exact PrimitiveSpectrum.isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactlyRepresented
      pi hpi
  · intro hAtomic
    refine ⟨PrimitiveSpectrum.ReducedAtomicHilbertSpace A, inferInstance, ?_⟩
    refine ⟨inferInstance, ?_⟩
    exact ⟨inferInstance, PrimitiveSpectrum.reducedAtomicRepresentation (A := A), hAtomic⟩

/-- A nonunital complex C-star algebra admits a faithful compact-valued
representation exactly when all its algebra-universe irreducible actions
have full compact range and its existing primitive spectrum is discrete.
An actual representation in another universe yields the same left side via
the canonical reduced atomic representation, not by shrinking its space. -/
theorem exists_isCompactlyRepresented_iff :
    (∃ (K : Type u) (normed : NormedAddCommGroup K),
      letI : NormedAddCommGroup K := normed
      ∃ inner : InnerProductSpace ℂ K,
        letI : InnerProductSpace ℂ K := inner
        ∃ complete : CompleteSpace K,
          letI : CompleteSpace K := complete
          ∃ pi : NonUnitalCStarRepresentation A K, pi.IsCompactlyRepresented) ↔
    (∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
      rho.IsIrreducible →
        (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) ∧
    DiscreteTopology (PrimitiveSpectrum A) :=
  (exists_isCompactlyRepresented_iff_reducedAtomicRepresentation (A := A)).trans
    (PrimitiveSpectrum.isCompactlyRepresented_reducedAtomicRepresentation_iff (A := A))

end NonUnitalCStarRepresentation

namespace PrimitiveSpectrum

/-- Moreover, any given faithful compact representation yields these facts
about the same pre-existing reduced atomic map: faithful compactness, both
literal diagonal range descriptions, isometry, norm preservation, coordinate
compression, and the adjoint identity. In particular its range is not
asserted to contain off-diagonal compact operators. -/
theorem reducedAtomicRepresentation_spec_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented ∧
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) ∧
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorBoundedProduct.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) ⊓
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          (ReducedAtomicHilbertSpace A) ∧
    Isometry (reducedAtomicRepresentation (A := A)) ∧
    (∀ a : A, ‖reducedAtomicRepresentation (A := A) a‖ = ‖a‖) ∧
    (∀ (a : A) (P : PrimitiveSpectrum A),
      (coordinateProjection P).comp
        ((reducedAtomicRepresentation (A := A) a).comp (coordinateEmbedding P)) =
          P.pureStateRepresentative.gnsRepresentation a) ∧
    (∀ a : A, ContinuousLinearMap.adjoint (reducedAtomicRepresentation (A := A) a) =
      reducedAtomicRepresentation (star a)) := by
  letI : DiscreteTopology (PrimitiveSpectrum A) :=
    discreteTopology_primitiveSpectrum_of_isCompactlyRepresented pi hpi
  have hSelected := range_pureStateRepresentative_eq_compact_of_isCompactlyRepresented pi hpi
  exact ⟨isCompactlyRepresented_reducedAtomicRepresentation hSelected,
    reducedAtomicRepresentation_range_eq_c0_diagonalRepresentation_range hSelected,
    reducedAtomicRepresentation_range_eq_bounded_diagonalRepresentation_range_inf_compactOperatorStarSubalgebra
      hSelected,
    isometry_reducedAtomicRepresentation (A := A),
    norm_reducedAtomicRepresentation (A := A),
    coordinateProjection_comp_reducedAtomicRepresentation_comp_coordinateEmbedding (A := A),
    adjoint_reducedAtomicRepresentation (A := A)⟩

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra

end
