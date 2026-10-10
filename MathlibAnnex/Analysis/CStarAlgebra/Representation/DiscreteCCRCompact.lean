/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.ReducedAtomic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactC0Model
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIdealRigidity
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactRange
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PrimitiveCompactRange

/-!
# Discrete CCR algebras and the same reduced atomic representation

The actual representation in this file is the existing
`PrimitiveSpectrum.reducedAtomicRepresentation`.  It is not a new witness
chosen from an existence theorem.  Under discreteness of the actual primitive
spectrum and literal compact range for the selected primitive GNS actions, its
coordinate c₀ equivalence gives exactly the composite used by
`CompactOperatorC0Sum.representationOfEquiv`.  Thus the same reduced atomic map
satisfies the existing `IsCompactlyRepresented` predicate.

The selected range condition is not silently called CCR.  A separate argument
first obtains it from compact range for all irreducible representations.  In
the other direction, compact-ideal rigidity transports a selected compact
range to any irreducible representation with that primitive kernel, in an
independent Hilbert universe.  Equality of kernels alone is not used as a
substitute for unitary equivalence: compact containment is an explicit input
to the rigidity theorem.  These bridges do not require discreteness.

Only the canonical spectral order is used to form the pre-existing pure-state
and primitive-spectrum objects.  It is installed locally, not made into an
extra order assumption on the algebra.  The quantified all-representation
condition at the end uses the universe of the algebra, which contains the
selected GNS spaces.  The pointwise converse is universe-polymorphic and
therefore recovers the compact range statement in every Hilbert universe.

The literal reduced atomic range is the c₀ block-diagonal range, or,
equivalently, the compact part of the bounded block-diagonal range.  It is not
identified with all compact operators on the Hilbert sum.  The bounded product,
the completed c₀ algebra and the Hilbert `lp 2` space remain distinct.  No
countability, separability, nonzero-algebra or nonzero-fiber assumption is added.
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

namespace PrimitiveSpectrum


end PrimitiveSpectrum

namespace NonUnitalCStarRepresentation


end NonUnitalCStarRepresentation

namespace PrimitiveSpectrum


/-- Compression of the same reduced atomic operator recovers the selected GNS
operator.  There is no CCR or discreteness assumption in this identity. -/
theorem coordinateProjection_comp_reducedAtomicRepresentation_comp_coordinateEmbedding
    (a : A) (P : PrimitiveSpectrum A) :
    (coordinateProjection P).comp
        ((reducedAtomicRepresentation (A := A) a).comp (coordinateEmbedding P)) =
      P.pureStateRepresentative.gnsRepresentation a := by
  apply ContinuousLinearMap.ext
  intro x
  change coordinateProjection P
    (reducedAtomicRepresentation a (coordinateEmbedding P x)) = _
  rw [reducedAtomicRepresentation_coordinateEmbedding]
  simp only [coordinateProjection_apply, coordinateEmbedding_apply,
    lp.coeFn_single, Pi.single_eq_same]

/-- The actual Hilbert adjoint is the reduced atomic image of the source star.
This is an identity of the existing representation, with no compactness input. -/
theorem adjoint_reducedAtomicRepresentation (a : A) :
    ContinuousLinearMap.adjoint (reducedAtomicRepresentation (A := A) a) =
      reducedAtomicRepresentation (star a) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (reducedAtomicRepresentation (A := A)) a).symm

/-- The existing faithful reduced atomic representation has closed literal
operator range, without assuming CCR or discreteness. -/
theorem isClosed_range_reducedAtomicRepresentation :
    IsClosed ((NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) :
      Set (ReducedAtomicHilbertSpace A →L[ℂ] ReducedAtomicHilbertSpace A)) := by
  change IsClosed (Set.range (reducedAtomicRepresentation (A := A)))
  exact (isometry_reducedAtomicRepresentation (A := A)).isClosedEmbedding.isClosed_range

section DiscreteCompactC0Proof

private abbrev discreteCompactC0NonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CompactC0Sum A) :=
  C0DirectSum.nonUnitalCStarAlgebra _

attribute [local instance] discreteCompactC0NonUnitalCStarAlgebra

private abbrev discreteCompactC0NormedAddCommGroup : NormedAddCommGroup (CompactC0Sum A) :=
  @NonUnitalNormedRing.toNormedAddCommGroup _
    discreteCompactC0NonUnitalCStarAlgebra.toNonUnitalNormedRing

attribute [local instance] discreteCompactC0NormedAddCommGroup

private abbrev discreteCompactC0SeminormedAddGroup : SeminormedAddGroup (CompactC0Sum A) :=
  @NormedAddGroup.toSeminormedAddGroup _
    (@NormedAddCommGroup.toNormedAddGroup _ discreteCompactC0NormedAddCommGroup)

attribute [local instance] discreteCompactC0SeminormedAddGroup

private abbrev discreteCompactC0Ring : NonUnitalRing (CompactC0Sum A) :=
  discreteCompactC0NonUnitalCStarAlgebra.toNonUnitalNormedRing.toNonUnitalRing

private abbrev discreteCompactC0NonAssocSemiring : NonUnitalNonAssocSemiring (CompactC0Sum A) :=
  discreteCompactC0Ring.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring

attribute [local instance] discreteCompactC0Ring discreteCompactC0NonAssocSemiring

private abbrev discreteCompactC0AddCommMonoid : AddCommMonoid (CompactC0Sum A) :=
  discreteCompactC0NonAssocSemiring.toAddCommMonoid

attribute [local instance] discreteCompactC0AddCommMonoid

private abbrev discreteCompactC0AddMonoid : AddMonoid (CompactC0Sum A) :=
  discreteCompactC0AddCommMonoid.toAddMonoid

attribute [local instance] discreteCompactC0AddMonoid

private abbrev discreteCompactC0Module : Module ℂ (CompactC0Sum A) :=
  discreteCompactC0NonUnitalCStarAlgebra.toNormedSpace.toModule

attribute [local instance] discreteCompactC0Module

private abbrev discreteCompactC0DistribMulAction : DistribMulAction ℂ (CompactC0Sum A) :=
  discreteCompactC0NonUnitalCStarAlgebra.toNormedSpace.toModule.toDistribMulAction

private abbrev discreteCompactC0AddZeroClass : AddZeroClass (CompactC0Sum A) :=
  discreteCompactC0NonAssocSemiring.toAddCommMonoid.toAddMonoid.toAddZeroClass

attribute [local instance] discreteCompactC0DistribMulAction discreteCompactC0AddZeroClass

private abbrev discreteCompactC0Zero : Zero (CompactC0Sum A) :=
  discreteCompactC0AddZeroClass.toZero

attribute [local instance] discreteCompactC0Zero

private abbrev discreteCompactC0Add : Add (CompactC0Sum A) :=
  discreteCompactC0AddZeroClass.toAddZero.toAdd

private abbrev discreteCompactC0Mul : Mul (CompactC0Sum A) :=
  discreteCompactC0NonAssocSemiring.toMulZeroClass.toMul

attribute [local instance] discreteCompactC0Add discreteCompactC0Mul

section Selected

variable [DiscreteTopology (PrimitiveSpectrum A)]
variable (hSelected : ∀ P : PrimitiveSpectrum A,
  (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
      P.pureStateRepresentative.GNS)

/-- The generic compact c₀-model representation is exactly the pre-existing
reduced atomic representation, as a bundled homomorphism, not just an
unspecified unitarily equivalent representation. -/
theorem representationOfEquiv_coordinateC0Equiv :
    CompactOperatorC0Sum.representationOfEquiv
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
        (coordinateC0Equiv hSelected) =
      reducedAtomicRepresentation (A := A) := by
  apply DFunLike.ext
  intro a
  exact c0_diagonalRepresentation_coordinateC0Equiv hSelected a

include hSelected in
/-- A discrete primitive spectrum with selected compact GNS ranges makes the
same reduced atomic representation faithfully compact.  The existing generic
c₀-model theorem is transported across the preceding literal map equality. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented := by
  have h := CompactOperatorC0Sum.isCompactlyRepresented_representationOfEquiv
    (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
    (coordinateC0Equiv hSelected)
  rw [representationOfEquiv_coordinateC0Equiv hSelected] at h
  exact h

/-- Applying the inverse coordinate equivalence to a specified c₀-family
recovers its actual diagonal operator under the same reduced atomic map. -/
theorem reducedAtomicRepresentation_coordinateC0Equiv_symm (x : CompactC0Sum A) :
    reducedAtomicRepresentation (A := A) ((coordinateC0Equiv hSelected).symm x) =
      CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS) x := by
  calc
    reducedAtomicRepresentation ((coordinateC0Equiv hSelected).symm x) =
        CompactOperatorC0Sum.diagonalRepresentation
          (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
          (coordinateC0Equiv hSelected ((coordinateC0Equiv hSelected).symm x)) :=
      (c0_diagonalRepresentation_coordinateC0Equiv hSelected
        ((coordinateC0Equiv hSelected).symm x)).symm
    _ = _ := congrArg
      (CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))
      ((coordinateC0Equiv hSelected).apply_symm_apply x)

/-- The pre-existing compact-codomain restriction and the generic compact
transport have the same values, including the same ambient operators. -/
theorem reducedAtomicCompactRepresentation_eq_compactRepresentationOfHom :
    reducedAtomicCompactRepresentation hSelected =
      CompactOperatorC0Sum.compactRepresentationOfHom
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
        (coordinateC0Equiv hSelected).toNonUnitalStarAlgHom := by
  apply DFunLike.ext
  intro a
  apply Subtype.ext
  change reducedAtomicRepresentation a =
    CompactOperatorC0Sum.diagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
      (coordinateC0Equiv hSelected a)
  exact (c0_diagonalRepresentation_coordinateC0Equiv hSelected a).symm

/-- Compact codomain restriction does not change the norm of the represented
element.  This is the norm of the same reduced atomic operator. -/
@[simp]
theorem norm_reducedAtomicCompactRepresentation (a : A) :
    ‖reducedAtomicCompactRepresentation hSelected a‖ = ‖a‖ := by
  change ‖reducedAtomicRepresentation (A := A) a‖ = ‖a‖
  exact norm_reducedAtomicRepresentation a

/-- The same compact-codomain restriction is an isometry. -/
theorem isometry_reducedAtomicCompactRepresentation :
    Isometry (reducedAtomicCompactRepresentation hSelected) :=
  AddMonoidHomClass.isometry_of_norm (reducedAtomicCompactRepresentation hSelected)
    (norm_reducedAtomicCompactRepresentation hSelected)

/-- In particular, the same compact-codomain map is faithful. -/
theorem reducedAtomicCompactRepresentation_injective :
    Function.Injective (reducedAtomicCompactRepresentation hSelected) :=
  (isometry_reducedAtomicCompactRepresentation hSelected).injective

set_option maxHeartbeats 8000000 in

/-- Inside the actual compact-operator algebra, the compact-codomain reduced
atomic range is exactly the compact diagonal range.  This is not an equality
with the entire compact-operator algebra. -/
theorem range_reducedAtomicCompactRepresentation_eq_range_compactDiagonalRepresentation :
    (NonUnitalStarAlgHom.range (reducedAtomicCompactRepresentation hSelected)) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.compactDiagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) := by
  apply SetLike.coe_injective
  change Set.range (reducedAtomicCompactRepresentation hSelected) =
    Set.range (CompactOperatorC0Sum.compactDiagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))
  let c : A → CompactC0Sum A := coordinateC0Equiv hSelected
  let d : CompactC0Sum A →
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (ReducedAtomicHilbertSpace A) :=
    CompactOperatorC0Sum.compactDiagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
  have hc : Function.Surjective c := EquivLike.surjective (coordinateC0Equiv hSelected)
  have hd : d ∘ c = (reducedAtomicCompactRepresentation hSelected) := by
    funext a
    apply Subtype.ext
    change CompactOperatorC0Sum.diagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
      (coordinateC0Equiv hSelected a) = reducedAtomicRepresentation a
    exact c0_diagonalRepresentation_coordinateC0Equiv hSelected a
  change Set.range (reducedAtomicCompactRepresentation hSelected) = Set.range d
  rw [← hd]
  exact hc.range_comp d

end Selected

section AllIrreducible

variable [DiscreteTopology (PrimitiveSpectrum A)]
variable (hCCR : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
  rho.IsIrreducible →
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)

include hCCR

/-- Discrete CCR, stated with actual ranges of all irreducible actions, implies
faithful compactness of the already named reduced atomic representation. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_forall_irreducible_range_eq_compact :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented :=
  isCompactlyRepresented_reducedAtomicRepresentation
    (range_pureStateRepresentative_eq_compact_of_forall_irreducible_range_eq_compact hCCR)

set_option maxHeartbeats 8000000 in

/-- The discrete all-irreducible CCR hypothesis yields the literal c₀ diagonal
range of the same reduced atomic representation. -/
theorem range_reducedAtomicRepresentation_eq_range_diagonalRepresentation_of_forall_irreducible_range_eq_compact :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) :=
  reducedAtomicRepresentation_range_eq_c0_diagonalRepresentation_range
    (range_pureStateRepresentative_eq_compact_of_forall_irreducible_range_eq_compact hCCR)

/-- Equivalently, the literal range is the compact intersection of the bounded
primitive block-diagonal range.  Off-diagonal compact operators are not claimed
to belong to this range. -/
theorem range_reducedAtomicRepresentation_eq_range_diagonalRepresentation_inf_compactOperatorStarSubalgebra_of_forall_irreducible_range_eq_compact :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorBoundedProduct.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) ⊓
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (ReducedAtomicHilbertSpace A) :=
  reducedAtomicRepresentation_range_eq_bounded_diagonalRepresentation_range_inf_compactOperatorStarSubalgebra
    (range_pureStateRepresentative_eq_compact_of_forall_irreducible_range_eq_compact hCCR)

end AllIrreducible

end DiscreteCompactC0Proof

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra
