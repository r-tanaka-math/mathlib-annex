/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.DiscreteCCR
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperatorDiagonal

/-!
# The reduced atomic representation on the genuine Hilbert direct sum

For a nonunital complex C-star algebra, choose the existing pure-state GNS
representative at every primitive point and form their completed dependent
Hilbert `lp 2` sum.  The corresponding atomic action is faithful because the
intersection of all primitive kernels is zero.  No countability or separability
assumption is imposed.

Under discreteness of the primitive spectrum and the stated CCR range equality,
the repaired coordinate equivalence identifies the algebra with the actual c₀
sum of compact primitive fibres.  The c₀ diagonal representation on the Hilbert
sum is then literally the reduced atomic representation.  Consequently its
image consists of compact operators, and its literal operator range agrees with
the c₀ diagonal range, equivalently with the compact intersection of the
bounded primitive block-diagonal range.  The bounded product `lp _ ∞`, the c₀
source algebra, and the Hilbert representation space `lp _ 2` remain distinct
objects.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u

namespace PrimitiveSpectrum

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The completed dependent Hilbert `lp 2` sum of the selected primitive GNS
spaces.  This is not the bounded product of compact-operator fibres. -/
abbrev ReducedAtomicHilbertSpace (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  HilbertSum (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)

/-- The selected primitive GNS representations acting diagonally on their
genuine completed Hilbert sum. -/
def reducedAtomicRepresentation :
    NonUnitalCStarRepresentation A (ReducedAtomicHilbertSpace A) :=
  (atomicRepresentation (fun P : PrimitiveSpectrum A =>
    P.pureStateRepresentative.gnsRepresentation.unitization)).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

@[simp]
theorem reducedAtomicRepresentation_apply
    (a : A) (x : ReducedAtomicHilbertSpace A) (P : PrimitiveSpectrum A) :
    reducedAtomicRepresentation a x P =
      P.pureStateRepresentative.gnsRepresentation a (x P) := by
  simp [reducedAtomicRepresentation, atomicRepresentation_apply, NonUnitalCStarRepresentation.unitization_inr]

/-- On one displayed primitive coordinate, the reduced atomic action is exactly
the selected GNS action. -/
@[simp]
theorem reducedAtomicRepresentation_coordinateEmbedding
    [DecidableEq (PrimitiveSpectrum A)] (a : A) (P : PrimitiveSpectrum A)
    (x : P.pureStateRepresentative.GNS) :
    reducedAtomicRepresentation a (coordinateEmbedding P x) =
      coordinateEmbedding P
        (P.pureStateRepresentative.gnsRepresentation a x) := by
  classical
  apply lp.ext
  funext Q
  by_cases hQP : Q = P
  · subst Q
    simp [reducedAtomicRepresentation_apply, coordinateEmbedding_apply,
      lp.coeFn_single]
  · simp [reducedAtomicRepresentation_apply, coordinateEmbedding_apply,
      lp.coeFn_single, hQP, Ne.symm hQP]

/-- Projection to one primitive coordinate commutes with the reduced atomic
action. -/
@[simp]
theorem coordinateProjection_reducedAtomicRepresentation
    [DecidableEq (PrimitiveSpectrum A)] (a : A) (x : ReducedAtomicHilbertSpace A) (P : PrimitiveSpectrum A) :
    coordinateProjection P (reducedAtomicRepresentation a x) =
      P.pureStateRepresentative.gnsRepresentation a
        (coordinateProjection P x) := by
  classical
  simp [coordinateProjection_apply, reducedAtomicRepresentation_apply]

/-- The reduced atomic representation is faithful: an element killed on every
selected primitive GNS space belongs to the intersection of all primitive
ideals, hence is zero. -/
theorem reducedAtomicRepresentation_injective :
    Function.Injective (reducedAtomicRepresentation (A := A)) := by
  classical
  intro a b hab
  apply sub_eq_zero.mp
  have hzero : reducedAtomicRepresentation (A := A) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hall : a - b ∈ kernelIntersection
      (Set.univ : Set (PrimitiveSpectrum A)) := by
    rw [mem_kernelIntersection]
    intro P _hP
    rw [← P.coe_toTwoSidedIdeal]
    rw [← P.kernelIdeal_pureStateRepresentative]
    apply (NonUnitalCStarRepresentation.mem_kernelIdeal
      P.pureStateRepresentative.gnsRepresentation (a - b)).2
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun T : ReducedAtomicHilbertSpace A →L[ℂ] ReducedAtomicHilbertSpace A =>
        coordinateProjection P (T (coordinateEmbedding P x))) hzero
    simpa [coordinateProjection_reducedAtomicRepresentation,
      coordinateEmbedding_apply, coordinateProjection_apply, lp.coeFn_single] using h
  rw [kernelIntersection_univ_eq_bot, TwoSidedIdeal.mem_bot] at hall
  exact hall

/-- Faithfulness upgrades the reduced atomic representation to an isometry. -/
theorem isometry_reducedAtomicRepresentation :
    Isometry (reducedAtomicRepresentation (A := A)) :=
  NonUnitalStarAlgHom.isometry (reducedAtomicRepresentation (A := A))
    reducedAtomicRepresentation_injective

@[simp]
theorem norm_reducedAtomicRepresentation (a : A) :
    ‖reducedAtomicRepresentation (A := A) a‖ = ‖a‖ := by
  simpa only [map_zero, dist_zero_right] using
    (isometry_reducedAtomicRepresentation (A := A)).dist_eq a 0

/-- Restriction of the faithful reduced atomic representation to its literal
operator range is onto. -/
theorem reducedAtomicRepresentation_rangeRestrict_surjective :
    Function.Surjective
      (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A))) := by
  intro T
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range
    (reducedAtomicRepresentation (A := A))).1 T.property
  exact ⟨a, Subtype.ext ha⟩

/-- The literal range restriction is bijective. -/
theorem reducedAtomicRepresentation_rangeRestrict_bijective :
    Function.Bijective
      (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A))) := by
  constructor
  · intro a b hab
    apply reducedAtomicRepresentation_injective
    exact congrArg Subtype.val hab
  · exact reducedAtomicRepresentation_rangeRestrict_surjective

/-- Actual nonunital C-star equivalence from `A` to the literal reduced atomic
operator range. -/
def reducedAtomicEquivRange :
    A ≃⋆ₐ[ℂ] (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) :=
  { Equiv.ofBijective (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A)))
      reducedAtomicRepresentation_rangeRestrict_bijective with
    map_add' := map_add (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A)))
    map_mul' := map_mul (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A)))
    map_smul' := map_smul (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A)))
    map_star' := map_star (NonUnitalStarAlgHom.rangeRestrict (reducedAtomicRepresentation (A := A))) }

@[simp]
theorem reducedAtomicEquivRange_apply_coe (a : A) :
    ((reducedAtomicEquivRange (A := A) a :
      (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A)))) :
        ReducedAtomicHilbertSpace A →L[ℂ] ReducedAtomicHilbertSpace A) =
      reducedAtomicRepresentation a := rfl

/-- The abstract bounded-product coordinate map acts on the Hilbert `lp 2` sum
as the reduced atomic representation.  This theorem connects the two different
`lp` constructions without identifying their types. -/
theorem boundedProduct_diagonalRepresentation_coordinateMap
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) :
    CompactOperatorBoundedProduct.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
        (coordinateMap hCCR a) =
      reducedAtomicRepresentation a := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext P
  simp only [CompactOperatorBoundedProduct.diagonalRepresentation_apply,
    coordinateMap_apply_coe, reducedAtomicRepresentation_apply]

/-- After the repaired range theorem and `coordinateC0Equiv`, the c₀ diagonal
representation is literally the reduced atomic representation. -/
theorem c0_diagonalRepresentation_coordinateC0Equiv
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) :
    CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
        (coordinateC0Equiv hCCR a) =
      reducedAtomicRepresentation a := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext P
  simp only [CompactOperatorC0Sum.diagonalRepresentation_apply,
    eval_coordinateC0Equiv_apply_coe, reducedAtomicRepresentation_apply]

section RangeC0Proof

private abbrev reducedAtomicC0NonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CompactC0Sum A) :=
  C0DirectSum.nonUnitalCStarAlgebra _

attribute [local instance] reducedAtomicC0NonUnitalCStarAlgebra

private abbrev reducedAtomicC0NormedAddCommGroup : NormedAddCommGroup (CompactC0Sum A) :=
  @NonUnitalNormedRing.toNormedAddCommGroup _
    reducedAtomicC0NonUnitalCStarAlgebra.toNonUnitalNormedRing

attribute [local instance] reducedAtomicC0NormedAddCommGroup

private abbrev reducedAtomicC0SeminormedAddGroup : SeminormedAddGroup (CompactC0Sum A) :=
  @NormedAddGroup.toSeminormedAddGroup _
    (@NormedAddCommGroup.toNormedAddGroup _ reducedAtomicC0NormedAddCommGroup)

attribute [local instance] reducedAtomicC0SeminormedAddGroup

private abbrev reducedAtomicC0Ring : NonUnitalRing (CompactC0Sum A) :=
  reducedAtomicC0NonUnitalCStarAlgebra.toNonUnitalNormedRing.toNonUnitalRing

private abbrev reducedAtomicC0NonAssocSemiring : NonUnitalNonAssocSemiring (CompactC0Sum A) :=
  reducedAtomicC0Ring.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring

attribute [local instance] reducedAtomicC0Ring reducedAtomicC0NonAssocSemiring

private abbrev reducedAtomicC0AddCommMonoid : AddCommMonoid (CompactC0Sum A) :=
  reducedAtomicC0NonAssocSemiring.toAddCommMonoid

attribute [local instance] reducedAtomicC0AddCommMonoid

private abbrev reducedAtomicC0AddMonoid : AddMonoid (CompactC0Sum A) :=
  reducedAtomicC0AddCommMonoid.toAddMonoid

attribute [local instance] reducedAtomicC0AddMonoid

private abbrev reducedAtomicC0Module : Module ℂ (CompactC0Sum A) :=
  reducedAtomicC0NonUnitalCStarAlgebra.toNormedSpace.toModule

attribute [local instance] reducedAtomicC0Module

private abbrev reducedAtomicC0DistribMulAction : DistribMulAction ℂ (CompactC0Sum A) :=
  reducedAtomicC0NonUnitalCStarAlgebra.toNormedSpace.toModule.toDistribMulAction

private abbrev reducedAtomicC0AddZeroClass : AddZeroClass (CompactC0Sum A) :=
  reducedAtomicC0NonAssocSemiring.toAddCommMonoid.toAddMonoid.toAddZeroClass

attribute [local instance] reducedAtomicC0DistribMulAction reducedAtomicC0AddZeroClass

private abbrev reducedAtomicC0Zero : Zero (CompactC0Sum A) :=
  reducedAtomicC0AddZeroClass.toZero

attribute [local instance] reducedAtomicC0Zero

private abbrev reducedAtomicC0Add : Add (CompactC0Sum A) :=
  reducedAtomicC0AddZeroClass.toAddZero.toAdd

private abbrev reducedAtomicC0Mul : Mul (CompactC0Sum A) :=
  reducedAtomicC0NonAssocSemiring.toMulZeroClass.toMul

attribute [local instance] reducedAtomicC0Add reducedAtomicC0Mul

set_option maxHeartbeats 8000000 in
/-- The literal Hilbert-operator range of the reduced atomic representation is
exactly the literal range of the compact c₀ diagonal representation. -/
theorem reducedAtomicRepresentation_range_eq_c0_diagonalRepresentation_range
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) := by
  apply SetLike.coe_injective
  change Set.range (reducedAtomicRepresentation (A := A)) =
    Set.range (CompactOperatorC0Sum.diagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))
  let c : A → CompactC0Sum A := coordinateC0Equiv hCCR
  let d : CompactC0Sum A →
      (ReducedAtomicHilbertSpace A →L[ℂ] ReducedAtomicHilbertSpace A) :=
    CompactOperatorC0Sum.diagonalRepresentation
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
  have hc : Function.Surjective c := EquivLike.surjective (coordinateC0Equiv hCCR)
  have hd : d ∘ c = (reducedAtomicRepresentation (A := A)) := by
    funext a
    dsimp only [Function.comp_apply, c, d]
    exact c0_diagonalRepresentation_coordinateC0Equiv hCCR a
  change Set.range (reducedAtomicRepresentation (A := A)) = Set.range d
  rw [← hd]
  exact hc.range_comp d

set_option maxHeartbeats 8000000 in
/-- Under discreteness and the selected CCR range equalities, the reduced
atomic operator range is exactly the compact part of the bounded primitive
block-diagonal range.  This remains a block-diagonal range statement and does
not assert surjectivity onto all compact operators on the Hilbert sum. -/
theorem reducedAtomicRepresentation_range_eq_bounded_diagonalRepresentation_range_inf_compactOperatorStarSubalgebra
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) =
      (NonUnitalStarAlgHom.range (CompactOperatorBoundedProduct.diagonalRepresentation
        (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS))) ⊓
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          (ReducedAtomicHilbertSpace A) := by
  exact (reducedAtomicRepresentation_range_eq_c0_diagonalRepresentation_range hCCR).trans
    (CompactOperatorBoundedProduct.diagonalRepresentation_range_inf_compactOperatorStarSubalgebra
      (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)).symm

end RangeC0Proof

/-- Under discreteness and the selected CCR range equalities, every reduced
atomic image operator is compact. -/
theorem isCompactOperator_reducedAtomicRepresentation
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) : IsCompactOperator (reducedAtomicRepresentation a) := by
  rw [← c0_diagonalRepresentation_coordinateC0Equiv hCCR a]
  exact CompactOperatorC0Sum.isCompactOperator_diagonalRepresentation
    (fun P : PrimitiveSpectrum A => P.pureStateRepresentative.GNS)
      (coordinateC0Equiv hCCR a)

/-- The reduced atomic operator range is contained in the concrete compact
operators on the completed Hilbert sum. -/
theorem reducedAtomicRepresentation_range_le_compactOperatorStarSubalgebra
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    (NonUnitalStarAlgHom.range (reducedAtomicRepresentation (A := A))) ≤
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        (ReducedAtomicHilbertSpace A) := by
  intro T hT
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range
    (reducedAtomicRepresentation (A := A))).1 hT
  rw [← ha]
  exact isCompactOperator_reducedAtomicRepresentation hCCR a

/-- The reduced atomic representation with codomain restricted to the actual
compact operators on the Hilbert sum. -/
def reducedAtomicCompactRepresentation
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    A →⋆ₙₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
      (ReducedAtomicHilbertSpace A) :=
  NonUnitalStarAlgHom.codRestrict (reducedAtomicRepresentation (A := A))
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
      (ReducedAtomicHilbertSpace A))
      (isCompactOperator_reducedAtomicRepresentation hCCR)

@[simp]
theorem reducedAtomicCompactRepresentation_apply_coe
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) :
    ((reducedAtomicCompactRepresentation hCCR a :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        (ReducedAtomicHilbertSpace A)) :
      ReducedAtomicHilbertSpace A →L[ℂ] ReducedAtomicHilbertSpace A) =
        reducedAtomicRepresentation a := rfl

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra
