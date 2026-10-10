/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.CompactModel
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicRestriction
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIntersection
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactlyRepresented

/-!
# Exact compact models from faithful irreducible compact representations

Restriction of a compact operator to a closed reducing subspace remains
compact.  Consequently the original-algebra cyclic restriction of a compact
representation still consists of compact operators.

The main result packages the converse direction needed by the generated-ideal
construction: a faithful irreducible representation all of whose operators are
compact has range exactly the compact-operator algebra.  The proof uses the
literal closed image and the compact-intersection theorem; surjectivity is not
introduced as a separate hypothesis.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- Compactness passes to the genuine restriction to a closed reducing
subspace. -/
theorem isCompactOperator_reducingRestriction
    (pi : NonUnitalCStarRepresentation A H)
    (hcompact : ∀ a : A, IsCompactOperator (pi a))
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M) (a : A) :
    IsCompactOperator (pi.reducingRestriction M hM a) := by
  change IsCompactOperator
    ((pi a).restrict (fun z hz => (hM.2 a z hz).1))
  exact (hcompact a).restrict' (fun z hz => (hM.2 a z hz).1)

/-- Every operator in an original-algebra cyclic restriction remains compact. -/
theorem isCompactOperator_cyclicRestriction
    (pi : NonUnitalCStarRepresentation A H)
    (hcompact : ∀ a : A, IsCompactOperator (pi a))
    (x : H) (a : A) :
    IsCompactOperator (pi.cyclicRestriction x a) := by
  exact pi.isCompactOperator_reducingRestriction hcompact
    (pi.cyclicSubspace x) (pi.reduces_cyclicSubspace x) a

/-- A nonzero orbit value makes the cyclic restriction a nonzero
representation.  The proof evaluates on the projected source vector, whose
original-algebra orbit is unchanged. -/
theorem isNonzero_cyclicRestriction_of_apply_ne_zero
    (pi : NonUnitalCStarRepresentation A H) {x : H} {a : A}
    (hax : pi a x ≠ 0) : (pi.cyclicRestriction x).IsNonzero := by
  refine ⟨a, ?_⟩
  intro hzero
  let v : pi.cyclicSubspace x :=
    (pi.cyclicSubspace x).orthogonalProjectionOnto x
  have hz := congrArg
    (fun T : pi.cyclicSubspace x →L[ℂ] pi.cyclicSubspace x => T v) hzero
  have hzval : ((pi.cyclicRestriction x a v : pi.cyclicSubspace x) : H) = 0 := by
    simpa using congrArg (fun z : pi.cyclicSubspace x => (z : H)) hz
  have hval : ((pi.cyclicRestriction x a v : pi.cyclicSubspace x) : H) = pi a x := by
    exact pi.apply_starProjection_cyclicSubspace x a
  exact hax (hval.symm.trans hzval)

/-- Faithfulness turns a nonzero source element into a genuinely nonzero
operator on some vector. -/
theorem exists_apply_ne_zero_of_injective
    (pi : NonUnitalCStarRepresentation A H) (hinj : Function.Injective pi)
    {a : A} (ha : a ≠ 0) : ∃ x : H, pi a x ≠ 0 := by
  have hmap : pi a ≠ 0 := by
    intro h
    exact ha (hinj (by simpa only [map_zero] using h))
  by_contra h
  apply hmap
  ext x
  simp only [ContinuousLinearMap.zero_apply]
  exact not_ne_iff.mp (not_exists.mp h x)

attribute [local instance] HomKernelQuotient.imageCStarAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.whnf.reducibleClassField false in
/-- A faithful irreducible representation consisting of compact operators is
an exact compact-operator model.  Equality of the concrete image with all
compact operators is proved, rather than assumed. -/
theorem isCompactOperatorModel_of_injective_of_isIrreducible_of_isCompactOperator
    (pi : NonUnitalCStarRepresentation A H)
    (hinj : Function.Injective pi) (hirr : pi.IsIrreducible)
    (hcompact : ∀ a : A, IsCompactOperator (pi a)) :
    IsCompactOperatorModel pi := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  have hclosed : IsClosed (NonUnitalStarAlgHom.range pi : Set (H →L[ℂ] H)) :=
    HomKernelQuotient.isClosed_image pi
  have hirrRange :
      NonUnitalCStarRepresentation.IsIrreducible
        (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)) := by
    simpa only [imageRepresentation] using
      (pi.isIrreducible_imageRepresentation_iff.mpr hirr)
  have hle : NonUnitalStarAlgHom.range pi ≤
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
    intro T hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hT
    exact hcompact a
  have heq : NonUnitalStarAlgHom.range pi =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
    eq_compactOperatorStarSubalgebra_of_le_of_isIrreducible
      (NonUnitalStarAlgHom.range pi) hclosed hirrRange hle
  refine ⟨hinj, hcompact, ?_⟩
  intro T hT
  apply (NonUnitalStarAlgHom.mem_range pi).1
  rw [heq]
  exact hT

/-- Compact representability becomes an exact compact model as soon as the
same faithful representation is known to be irreducible. -/
theorem IsCompactlyRepresented.isCompactOperatorModel_of_isIrreducible
    {pi : NonUnitalCStarRepresentation A H}
    (hpi : pi.IsCompactlyRepresented) (hirr : pi.IsIrreducible) :
    IsCompactOperatorModel pi :=
  pi.isCompactOperatorModel_of_injective_of_isIrreducible_of_isCompactOperator
    hpi.1 hirr hpi.2

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
