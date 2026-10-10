/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CoordinateIdeal
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.BoundedProductIdeal
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.PrimitiveCoordinate

/-!
# Discrete CCR algebras as c₀-sums of compact coordinate fibres

For a possibly nonunital complex C-star algebra whose actual primitive spectrum
is discrete, assume that every selected pure-state GNS representation has
literal compact-operator range.  The selected GNS actions assemble first into
the genuine dependent bounded product of the compact fibres.  Primitive-kernel
separation proves this map faithful.  Isolated primitive-coordinate ideals
supply every single-coordinate compact family, so the actual dependent c₀-sum
lies in the closed range.

The c₀-subalgebra is proved to be a norm-closed two-sided ideal in both the
bounded product and the actual coordinate-map range.  If that range ideal were
proper, the general primitive separator applied to the range would pull back to
an irreducible representation of the original algebra.  Its own isolated
coordinate ideal then gives a nonzero element which the separator must kill, a
contradiction.  Hence the bounded-product range is exactly the actual c₀-sum,
and the coordinate map is an actual nonunital C-star algebra equivalence.

No countability or separability assumption is imposed.  The bounded product,
its c₀-ideal, and the c₀-direct sum remain distinct objects until the proved
range equality.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.whnf.reducibleClassField true
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u uK


namespace PrimitiveSpectrum

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual compact-operator fibre selected by a primitive point. -/
abbrev CompactFiber (P : PrimitiveSpectrum A) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
    P.pureStateRepresentative.GNS

/-- The genuine dependent bounded product of all selected primitive compact
fibres. -/
abbrev CompactBoundedProduct (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  lp (fun P : PrimitiveSpectrum A => CompactFiber P) ∞

@[implicit_reducible] private def compactProductNormedAddCommGroup : NormedAddCommGroup (CompactBoundedProduct A) :=
  lp.normedAddCommGroup

attribute [local instance] compactProductNormedAddCommGroup

@[implicit_reducible] private def compactProductCStar : NonUnitalCStarAlgebra (CompactBoundedProduct A) :=
  inferInstance

attribute [local instance] compactProductCStar

@[implicit_reducible] private def compactProductModule : Module ℂ (CompactBoundedProduct A) :=
  compactProductCStar.toNormedSpace.toModule

@[implicit_reducible] private def compactProductDistribMulAction : DistribMulAction ℂ (CompactBoundedProduct A) :=
  compactProductModule.toDistribMulAction

attribute [local instance] compactProductModule compactProductDistribMulAction

@[implicit_reducible] private def compactProductRing : NonUnitalRing (CompactBoundedProduct A) :=
  compactProductCStar.toNonUnitalNormedRing.toNonUnitalRing

@[implicit_reducible] private def compactProductNonAssocSemiring :
    NonUnitalNonAssocSemiring (CompactBoundedProduct A) :=
  compactProductRing.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring

attribute [local instance] compactProductRing compactProductNonAssocSemiring

@[implicit_reducible] private def compactProductSeminormedAddGroup : SeminormedAddGroup (CompactBoundedProduct A) :=
  @NormedAddGroup.toSeminormedAddGroup _
    (@NormedAddCommGroup.toNormedAddGroup _ compactProductNormedAddCommGroup)

attribute [local instance] compactProductSeminormedAddGroup

/-- The genuine dependent c₀-sum of all selected primitive compact fibres. -/
abbrev CompactC0Sum (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  C0DirectSum (fun P : PrimitiveSpectrum A => CompactFiber P)

@[implicit_reducible] private def compactC0NonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CompactC0Sum A) :=
  C0DirectSum.nonUnitalCStarAlgebra _

attribute [local instance] compactC0NonUnitalCStarAlgebra

@[implicit_reducible] private def compactC0NormedAddCommGroup : NormedAddCommGroup (CompactC0Sum A) :=
  @NonUnitalNormedRing.toNormedAddCommGroup _
    compactC0NonUnitalCStarAlgebra.toNonUnitalNormedRing

attribute [local instance] compactC0NormedAddCommGroup

@[implicit_reducible] private def compactC0SeminormedAddGroup : SeminormedAddGroup (CompactC0Sum A) :=
  @NormedAddGroup.toSeminormedAddGroup _
    (@NormedAddCommGroup.toNormedAddGroup _ compactC0NormedAddCommGroup)

attribute [local instance] compactC0SeminormedAddGroup

@[implicit_reducible] private def compactC0Ring : NonUnitalRing (CompactC0Sum A) :=
  compactC0NonUnitalCStarAlgebra.toNonUnitalNormedRing.toNonUnitalRing

@[implicit_reducible] private def compactC0NonAssocSemiring : NonUnitalNonAssocSemiring (CompactC0Sum A) :=
  compactC0Ring.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring

attribute [local instance] compactC0Ring compactC0NonAssocSemiring

@[implicit_reducible] private def compactC0AddCommMonoid : AddCommMonoid (CompactC0Sum A) :=
  compactC0NonAssocSemiring.toAddCommMonoid

attribute [local instance] compactC0AddCommMonoid

@[implicit_reducible] private def compactC0AddMonoid : AddMonoid (CompactC0Sum A) :=
  compactC0AddCommMonoid.toAddMonoid

attribute [local instance] compactC0AddMonoid

@[implicit_reducible] private def compactC0Module : Module ℂ (CompactC0Sum A) :=
  compactC0NonUnitalCStarAlgebra.toNormedSpace.toModule

attribute [local instance] compactC0Module

@[implicit_reducible] private def compactC0DistribMulAction : DistribMulAction ℂ (CompactC0Sum A) :=
  compactC0NonUnitalCStarAlgebra.toNormedSpace.toModule.toDistribMulAction

@[implicit_reducible] private def compactC0AddZeroClass : AddZeroClass (CompactC0Sum A) :=
  compactC0NonAssocSemiring.toAddCommMonoid.toAddMonoid.toAddZeroClass

attribute [local instance] compactC0DistribMulAction compactC0AddZeroClass

@[implicit_reducible] private def compactC0Zero : Zero (CompactC0Sum A) :=
  compactC0AddZeroClass.toZero

attribute [local instance] compactC0Zero

/-- The simultaneous selected-GNS coordinate map into the actual bounded
product.  Membership in each compact fibre is supplied by the stated CCR
range equality; boundedness is the contractivity of C-star homomorphisms. -/
def coordinateMap
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    A →⋆ₙₐ[ℂ] CompactBoundedProduct A where
  toFun a := by
    refine ⟨fun P => ⟨P.pureStateRepresentative.gnsRepresentation a, ?_⟩,
      memℓp_infty ?_⟩
    · change P.pureStateRepresentative.gnsRepresentation a ∈
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ P.pureStateRepresentative.GNS
      rw [← hCCR P]
      exact (NonUnitalStarAlgHom.mem_range
        P.pureStateRepresentative.gnsRepresentation).2 ⟨a, rfl⟩
    · refine ⟨‖a‖, ?_⟩
      rintro r ⟨P, rfl⟩
      exact NonUnitalStarAlgHom.norm_apply_le
        P.pureStateRepresentative.gnsRepresentation a
  map_zero' := by
    apply lp.ext
    funext P
    apply Subtype.ext
    exact map_zero P.pureStateRepresentative.gnsRepresentation
  map_add' a b := by
    apply lp.ext
    funext P
    apply Subtype.ext
    exact map_add P.pureStateRepresentative.gnsRepresentation a b
  map_mul' a b := by
    apply lp.ext
    funext P
    apply Subtype.ext
    exact map_mul P.pureStateRepresentative.gnsRepresentation a b
  map_smul' c a := by
    apply lp.ext
    funext P
    apply Subtype.ext
    exact map_smul P.pureStateRepresentative.gnsRepresentation c a
  map_star' a := by
    apply lp.ext
    funext P
    apply Subtype.ext
    exact map_star P.pureStateRepresentative.gnsRepresentation a

@[simp]
theorem coordinateMap_apply_coe
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) (P : PrimitiveSpectrum A) :
    (((coordinateMap hCCR a) P : CompactFiber P) :
      P.pureStateRepresentative.GNS →L[ℂ] P.pureStateRepresentative.GNS) =
        P.pureStateRepresentative.gnsRepresentation a := rfl

/-- The simultaneous coordinate map is contractive in the inherited supremum
norm. -/
theorem norm_coordinateMap_le
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) : ‖coordinateMap hCCR a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (coordinateMap hCCR) a

/-- Primitive-kernel separation makes the simultaneous coordinate map
faithful. -/
theorem coordinateMap_injective
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    Function.Injective (coordinateMap hCCR) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hzero : coordinateMap hCCR (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hall : a - b ∈ kernelIntersection
      (Set.univ : Set (PrimitiveSpectrum A)) := by
    rw [mem_kernelIntersection]
    intro P _hP
    rw [← P.coe_toTwoSidedIdeal]
    rw [← P.kernelIdeal_pureStateRepresentative]
    apply (NonUnitalCStarRepresentation.mem_kernelIdeal
      P.pureStateRepresentative.gnsRepresentation (a - b)).2
    have hcoord := congrArg
      (fun x : CompactBoundedProduct A =>
        (((x P : CompactFiber P) :
          P.pureStateRepresentative.GNS →L[ℂ]
            P.pureStateRepresentative.GNS))) hzero
    simpa only [coordinateMap_apply_coe, lp.coeFn_zero, Pi.zero_apply,
      ZeroMemClass.coe_zero] using hcoord
  rw [kernelIntersection_univ_eq_bot, TwoSidedIdeal.mem_bot] at hall
  exact hall

/-- Faithfulness upgrades the coordinate map to an isometry. -/
theorem isometry_coordinateMap
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    Isometry (coordinateMap hCCR) :=
  NonUnitalStarAlgHom.isometry (coordinateMap hCCR)
    (coordinateMap_injective hCCR)

@[simp]
theorem norm_coordinateMap
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) : ‖coordinateMap hCCR a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map (coordinateMap hCCR)
    (coordinateMap_injective hCCR) a

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The faithful coordinate-map range is norm closed in the actual bounded
product. -/
theorem isClosed_coordinateMap_range
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    IsClosed ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) :=
  HomKernelQuotient.isClosed_image (coordinateMap hCCR)

open scoped Classical

/-- Every compact operator in one primitive fibre occurs as an actual
single-coordinate bounded family in the simultaneous coordinate-map range. -/
theorem lp_single_mem_coordinateMap_range
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (P : PrimitiveSpectrum A) (T : CompactFiber P) :
    (lp.single (E := fun Q : PrimitiveSpectrum A => CompactFiber Q) ∞ P T : CompactBoundedProduct A) ∈ ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) := by
  have hT : (T : P.pureStateRepresentative.GNS →L[ℂ]
      P.pureStateRepresentative.GNS) ∈ (NonUnitalStarAlgHom.range P.coordinateRepresentation) := by
    rw [P.coordinateRepresentation_range_eq_compactOperatorStarSubalgebra (hCCR P)]
    exact T.property
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range P.coordinateRepresentation).1 hT
  apply (NonUnitalStarAlgHom.mem_range (coordinateMap hCCR)).2
  refine ⟨a.1, ?_⟩
  apply lp.ext
  funext Q
  apply Subtype.ext
  by_cases hQP : Q = P
  · subst Q
    simpa [coordinateMap_apply_coe, lp.single_apply] using ha
  · have haQ : a.1 ∈ Q.toTwoSidedIdeal :=
      (mem_toTwoSidedIdeal Q a.1).2
        ((mem_coordinateIdeal P a.1).1 a.2 Q hQP)
    have hz : Q.pureStateRepresentative.gnsRepresentation a.1 = 0 :=
      (NonUnitalCStarRepresentation.mem_kernelIdeal
        Q.pureStateRepresentative.gnsRepresentation a.1).1 (by
          simpa only [Q.kernelIdeal_pureStateRepresentative] using haQ)
    simpa [coordinateMap_apply_coe, lp.single_apply, hQP, Ne.symm hQP] using hz

/-- Every finite coordinate truncation of an actual c₀-family lies in the
simultaneous coordinate-map range. -/
theorem truncate_coe_mem_coordinateMap_range
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (s : Finset (PrimitiveSpectrum A)) (x : CompactC0Sum A) :
    ((C0DirectSum.truncate (fun P : PrimitiveSpectrum A => CompactFiber P) s x :
      CompactC0Sum A) : CompactBoundedProduct A) ∈ ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) := by
  classical
  change (NonUnitalStarSubalgebraClass.subtype
    (C0DirectSum.starSubalgebra (fun P : PrimitiveSpectrum A => CompactFiber P)))
      (∑ P ∈ s, C0DirectSum.single
        (fun Q : PrimitiveSpectrum A => CompactFiber Q) P
        (C0DirectSum.eval (fun Q : PrimitiveSpectrum A => CompactFiber Q) P x)) ∈
      ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A))
  rw [map_sum]
  exact sum_mem fun P _ => lp_single_mem_coordinateMap_range hCCR P
    (C0DirectSum.eval (fun Q : PrimitiveSpectrum A => CompactFiber Q) P x)

set_option maxHeartbeats 32000000 in
/-- The actual c₀-sum is contained in the norm-closed simultaneous coordinate
range. -/
theorem c0_coe_mem_coordinateMap_range
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (x : CompactC0Sum A) :
    x.val ∈ ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) := by
  change x.val ∈
    ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A))
  rw [← (isClosed_coordinateMap_range hCCR).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := C0DirectSum.exists_finset_norm_sub_truncate_lt
    (fun P : PrimitiveSpectrum A => CompactFiber P) x hε
  refine ⟨(C0DirectSum.truncate
      (fun P : PrimitiveSpectrum A => CompactFiber P) s x : CompactC0Sum A),
    truncate_coe_mem_coordinateMap_range hCCR s x, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (C0DirectSum.truncate
    (fun P : PrimitiveSpectrum A => CompactFiber P) s x).val‖ < ε
  change ‖x.val - (C0DirectSum.truncate
    (fun P : PrimitiveSpectrum A => CompactFiber P) s x).val‖ < ε at hs
  exact hs

@[implicit_reducible] private def coordinateRangeRing
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    NonUnitalRing (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
  NonUnitalStarSubalgebra.toNonUnitalRing _

attribute [local instance] coordinateRangeRing

@[implicit_reducible] private def coordinateRangeNonAssocRing
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    NonUnitalNonAssocRing (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
  (coordinateRangeRing hCCR).toNonUnitalNonAssocRing

attribute [local instance] coordinateRangeNonAssocRing

@[implicit_reducible] private def coordinateRangeNonAssocSemiring
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    NonUnitalNonAssocSemiring (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
  (coordinateRangeNonAssocRing hCCR).toNonUnitalNonAssocSemiring

attribute [local instance] coordinateRangeNonAssocSemiring

/-- The c₀-carrier, pulled back to the actual simultaneous coordinate-map
range, is a genuine algebraic two-sided ideal. -/
def coordinateRangeC0Ideal
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    TwoSidedIdeal (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
  TwoSidedIdeal.mk'
    {x | C0DirectSum.VanishesAtInfinity
      (fun P : PrimitiveSpectrum A => CompactFiber P) x.1}
    (C0DirectSum.vanishesAtInfinity_zero _)
    (fun hx hy => hx.add (A := fun P : PrimitiveSpectrum A => CompactFiber P) hy)
    (fun hx => hx.neg (A := fun P : PrimitiveSpectrum A => CompactFiber P))
    (fun hy => hy.mul_left_bounded
      (A := fun P : PrimitiveSpectrum A => CompactFiber P) _)
    (fun hx => hx.mul_right_bounded
      (A := fun P : PrimitiveSpectrum A => CompactFiber P) _)

@[simp]
theorem mem_coordinateRangeC0Ideal
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (x : (NonUnitalStarAlgHom.range (coordinateMap hCCR))) :
    x ∈ coordinateRangeC0Ideal hCCR ↔
      C0DirectSum.VanishesAtInfinity
        (fun P : PrimitiveSpectrum A => CompactFiber P) x.1 := by
  simp [coordinateRangeC0Ideal]

/-- The c₀-ideal inside the coordinate-map range is norm closed. -/
theorem isClosed_coordinateRangeC0Ideal
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    IsClosed (coordinateRangeC0Ideal hCCR : Set (NonUnitalStarAlgHom.range (coordinateMap hCCR))) := by
  have hcarrier :
      (coordinateRangeC0Ideal hCCR : Set (NonUnitalStarAlgHom.range (coordinateMap hCCR))) =
        {x | C0DirectSum.VanishesAtInfinity
          (fun P : PrimitiveSpectrum A => CompactFiber P) x.val} :=
    Set.ext fun x => mem_coordinateRangeC0Ideal hCCR x
  rw [hcarrier]
  exact (C0DirectSum.isClosed_setOf_vanishesAtInfinity
    (fun P : PrimitiveSpectrum A => CompactFiber P)).preimage continuous_subtype_val

/-- Elements of an isolated primitive-coordinate ideal map into the actual c₀
ideal of the simultaneous range. -/
theorem rangeRestrict_mem_coordinateRangeC0Ideal_of_mem_coordinateIdeal
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (P : PrimitiveSpectrum A) {a : A} (ha : a ∈ P.coordinateIdeal) :
    (NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR)) a ∈ coordinateRangeC0Ideal hCCR := by
  rw [mem_coordinateRangeC0Ideal]
  intro ε hε
  refine (Set.finite_singleton P).subset ?_
  intro Q hQ
  simp only [Set.mem_singleton_iff]
  by_contra hQP
  have haQ : a ∈ Q.toTwoSidedIdeal := by
    exact (mem_toTwoSidedIdeal Q a).2
      ((mem_coordinateIdeal P a).1 ha Q hQP)
  have hz : Q.pureStateRepresentative.gnsRepresentation a = 0 :=
    (NonUnitalCStarRepresentation.mem_kernelIdeal
      Q.pureStateRepresentative.gnsRepresentation a).1 (by
        simpa only [Q.kernelIdeal_pureStateRepresentative] using haQ)
  change ε ≤ ‖(((coordinateMap hCCR a) Q : CompactFiber Q) :
    Q.pureStateRepresentative.GNS →L[ℂ] Q.pureStateRepresentative.GNS)‖ at hQ
  rw [coordinateMap_apply_coe, hz, norm_zero] at hQ
  exact (not_lt_of_ge hQ) hε

/-- The range restriction of the coordinate map is surjective onto its literal
range. -/
theorem coordinateMap_rangeRestrict_surjective
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    Function.Surjective (NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR)) := by
  intro x
  have hx : ∃ a : A, coordinateMap hCCR a = x.val := x.property
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, Subtype.ext ha⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.whnf.reducibleClassField false in
set_option maxHeartbeats 32000000 in
/-- The c₀-ideal inside the faithful coordinate range cannot be proper.  The
proof applies the general primitive separator to a hypothetical point outside
it, pulls the separator back through the actual surjective range restriction,
and contradicts the isolated coordinate ideal of the resulting primitive
kernel. -/
theorem coordinateRangeC0Ideal_eq_top
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    coordinateRangeC0Ideal hCCR = (⊤ : TwoSidedIdeal (NonUnitalStarAlgHom.range (coordinateMap hCCR))) := by
  apply TwoSidedIdeal.ext
  intro y
  constructor
  · intro _hy
    exact TwoSidedIdeal.mem_top _
  · intro _hy
    by_contra hyJ
    letI rangeCStar : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
      HomKernelQuotient.imageCStarAlgebra (coordinateMap hCCR)
    letI rangeModule : Module ℂ (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
      rangeCStar.toNormedSpace.toModule
    letI : DistribMulAction ℂ (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
      rangeModule.toDistribMulAction
    letI : StarRing (NonUnitalStarAlgHom.range (coordinateMap hCCR)) :=
      rangeCStar.toStarRing
    obtain ⟨K, instN, instI, instC, rho, hrho, hJrho, hy0⟩ :=
      exists_isIrreducible_ker_ge_and_apply_ne_zero
        (coordinateRangeC0Ideal hCCR)
        (isClosed_coordinateRangeC0Ideal hCCR) y hyJ
    letI : NormedAddCommGroup K := instN
    letI : InnerProductSpace ℂ K := instI
    letI : CompleteSpace K := instC
    let sigma : NonUnitalCStarRepresentation A K :=
      rho.comp (NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR))
    have hsigma : sigma.IsIrreducible :=
      (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective rho
        (NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR))
        (coordinateMap_rangeRestrict_surjective hCCR)).2 hrho
    let P : PrimitiveSpectrum A := PrimitiveSpectrum.ofRepresentation sigma hsigma
    obtain ⟨a, haJ, haP⟩ := P.exists_mem_coordinateIdeal_not_mem_toTwoSidedIdeal
    have hmem : (NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR)) a ∈ coordinateRangeC0Ideal hCCR :=
      rangeRestrict_mem_coordinateRangeC0Ideal_of_mem_coordinateIdeal hCCR P haJ
    have hzeroRange : rho ((NonUnitalStarAlgHom.rangeRestrict (coordinateMap hCCR)) a) = 0 :=
      (TwoSidedIdeal.mem_ker rho).1 (hJrho hmem)
    have hzero : sigma a = 0 := hzeroRange
    apply haP
    rw [mem_toTwoSidedIdeal]
    change a ∈ (NonUnitalCStarRepresentation.kernelIdeal sigma : Set A)
    exact (NonUnitalCStarRepresentation.mem_kernelIdeal sigma a).2 hzero

/-- The literal bounded-product range of the simultaneous coordinate map is
exactly the actual c₀-carrier. -/
theorem coordinateMap_range_eq_c0_carrier
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) =
      C0DirectSum.starSubalgebra
        (fun P : PrimitiveSpectrum A => CompactFiber P) := by
  ext x
  constructor
  · intro hx
    let xr : (NonUnitalStarAlgHom.range (coordinateMap hCCR)) := ⟨x, hx⟩
    have hmem : xr ∈ coordinateRangeC0Ideal hCCR := by
      rw [coordinateRangeC0Ideal_eq_top hCCR]
      exact TwoSidedIdeal.mem_top (NonUnitalStarAlgHom.range (coordinateMap hCCR))
    exact (mem_coordinateRangeC0Ideal hCCR xr).1 hmem
  · intro hx
    exact c0_coe_mem_coordinateMap_range hCCR ⟨x, hx⟩

/-- The coordinate map with its codomain restricted to the actual dependent
c₀-sum. -/
def coordinateC0Map
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    A →⋆ₙₐ[ℂ] CompactC0Sum A :=
  NonUnitalStarAlgHom.codRestrict (coordinateMap hCCR)
    (C0DirectSum.starSubalgebra
      (fun P : PrimitiveSpectrum A => CompactFiber P)) fun a => by
        change coordinateMap hCCR a ∈
          ((C0DirectSum.starSubalgebra
            (fun P : PrimitiveSpectrum A => CompactFiber P)) : Set (CompactBoundedProduct A))
        rw [← coordinateMap_range_eq_c0_carrier hCCR]
        exact (NonUnitalStarAlgHom.mem_range (coordinateMap hCCR)).2 ⟨a, rfl⟩

@[simp]
theorem coordinateC0Map_apply_coe
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) :
    ((coordinateC0Map hCCR a : CompactC0Sum A) : CompactBoundedProduct A) =
      coordinateMap hCCR a := rfl

/-- The actual c₀-valued coordinate map is bijective. -/
theorem coordinateC0Map_bijective
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    Function.Bijective (coordinateC0Map hCCR) := by
  constructor
  · intro a b hab
    apply coordinateMap_injective hCCR
    exact congrArg Subtype.val hab
  · intro x
    have hx : x.val ∈ ((NonUnitalStarAlgHom.range (coordinateMap hCCR)) : Set (CompactBoundedProduct A)) :=
      c0_coe_mem_coordinateMap_range hCCR x
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range (coordinateMap hCCR)).1 hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

/-- The actual C-star equivalence between the original discrete CCR algebra and
the dependent c₀-sum of its selected compact primitive fibres. -/
def coordinateC0Equiv
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) :
    A ≃⋆ₐ[ℂ] CompactC0Sum A :=
  { Equiv.ofBijective (coordinateC0Map hCCR) (coordinateC0Map_bijective hCCR) with
    map_add' := (coordinateC0Map hCCR).toNonUnitalAlgHom.map_add'
    map_mul' := map_mul (coordinateC0Map hCCR)
    map_smul' := (coordinateC0Map hCCR).toNonUnitalAlgHom.map_smul'
    map_star' := map_star (coordinateC0Map hCCR) }

@[simp]
theorem eval_coordinateC0Equiv_apply_coe
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) (P : PrimitiveSpectrum A) :
    ((C0DirectSum.eval (fun Q : PrimitiveSpectrum A => CompactFiber Q) P
      (coordinateC0Equiv hCCR a) : CompactFiber P) :
        P.pureStateRepresentative.GNS →L[ℂ]
          P.pureStateRepresentative.GNS) =
      P.pureStateRepresentative.gnsRepresentation a := rfl

@[simp]
theorem norm_coordinateC0Equiv
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) : ‖coordinateC0Equiv hCCR a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map
    (coordinateC0Equiv hCCR) (coordinateC0Equiv hCCR).injective a

@[simp]
theorem coordinateC0Equiv_symm_apply_apply
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (a : A) :
    (coordinateC0Equiv hCCR).symm (coordinateC0Equiv hCCR a) = a :=
  (coordinateC0Equiv hCCR).left_inv a

@[simp]
theorem coordinateC0Equiv_apply_symm_apply
    [DiscreteTopology (PrimitiveSpectrum A)]
    (hCCR : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS)
    (x : CompactC0Sum A) :
    coordinateC0Equiv hCCR ((coordinateC0Equiv hCCR).symm x) = x :=
  (coordinateC0Equiv hCCR).right_inv x

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra
