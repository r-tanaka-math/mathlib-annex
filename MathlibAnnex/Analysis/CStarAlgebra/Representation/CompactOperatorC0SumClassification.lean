/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.C0DirectSum
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperatorC0Sum
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactRange
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationEquivalence

/-!
# Classification of irreducible representations of compact-operator c₀-sums

Every nonzero irreducible representation of a dependent c₀-sum of compact
operator algebras has one and only one active coordinate.  The restriction to
that compact fibre is proved irreducible, classified by the concrete compact
operator representation, and the same unitary is then shown to intertwine the
whole c₀-sum action.  Equality of kernels alone is never used as a substitute
for the actual unitary equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uH uK

namespace CompactOperatorC0Sum

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]

private abbrev ClassificationFiber (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

/-- The active fibre representation obtained by restricting a representation of
the whole c₀-sum along one coordinate embedding. -/
def fiberRestriction {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K) (i : ι) :
    NonUnitalCStarRepresentation (ClassificationFiber H i) K :=
  rho.comp (C0DirectSum.single (fun j => ClassificationFiber H j) i)

@[simp]
theorem fiberRestriction_apply {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (i : ι) (a : ClassificationFiber H i) :
    fiberRestriction H rho i a =
      rho (C0DirectSum.single (fun j => ClassificationFiber H j) i a) := rfl

/-- The active fibre restriction is irreducible; this is a consequence of the
irreducibility of the whole action and the coordinate-complement decomposition. -/
theorem isIrreducible_fiberRestriction_of_isNonzero {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) (i : ι)
    (hi : (fiberRestriction H rho i).IsNonzero) :
    (fiberRestriction H rho i).IsIrreducible := by
  exact C0DirectSum.isIrreducible_comp_single_of_isNonzero
    (fun j => ClassificationFiber H j) rho hrho i hi

/-- The coordinate representation has exactly the compact operators as its
literal range. -/
theorem range_coordinateRepresentation (i : ι) :
    (NonUnitalStarAlgHom.range (coordinateRepresentation H i)) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i) := by
  apply le_antisymm
  · intro T hT
    obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range (coordinateRepresentation H i)).1 hT
    change IsCompactOperator T
    rw [← hx]
    exact (coordinateEvaluation H i x).property
  · intro T hT
    let a : ClassificationFiber H i := ⟨T, hT⟩
    let x : CompactOperatorC0Sum H :=
      C0DirectSum.single (fun j => ClassificationFiber H j) i a
    apply (NonUnitalStarAlgHom.mem_range (coordinateRepresentation H i)).2
    refine ⟨x, ?_⟩
    have hs := coordinateRepresentation_single_same H i a
    simpa [a, x, compactOperatorRepresentation] using hs

/-- A nonzero active coordinate supplies an actual unitary equivalence from the
coordinate representation to the whole irreducible action. -/
theorem unitaryEquivalent_coordinateRepresentation_of_isNonzero_fiberRestriction
    {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) (i : ι)
    (hi : (fiberRestriction H rho i).IsNonzero) :
    (coordinateRepresentation H i).UnitaryEquivalent rho := by
  have hirr : (fiberRestriction H rho i).IsIrreducible :=
    isIrreducible_fiberRestriction_of_isNonzero H rho hrho i hi
  obtain ⟨U, hU⟩ := unitaryEquivalent_compactOperatorRepresentation
    (fiberRestriction H rho i) hirr
  refine ⟨U, ?_⟩
  intro x v
  have hcoord := C0DirectSum.apply_eq_apply_single_eval_of_isNonzero_comp_single
    (fun j => ClassificationFiber H j) rho hrho i hi x
  calc
    U (coordinateRepresentation H i x v) =
        (fiberRestriction H rho i) (coordinateEvaluation H i x) (U v) := by
      exact hU (coordinateEvaluation H i x) v
    _ = rho (C0DirectSum.single (fun j => ClassificationFiber H j) i
          (C0DirectSum.eval (fun j => ClassificationFiber H j) i x)) (U v) := rfl
    _ = rho x (U v) := by
      exact congrArg (fun T : K →L[ℂ] K => T (U v)) hcoord.symm

/-- Every nonzero irreducible representation is actually unitarily equivalent
to a coordinate representation. -/
theorem exists_coordinate_unitaryEquivalent {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) :
    ∃ i : ι, (coordinateRepresentation H i).UnitaryEquivalent rho := by
  obtain ⟨i, hi⟩ := C0DirectSum.exists_isNonzero_comp_single
    (fun j => ClassificationFiber H j) rho hrho.1
  exact ⟨i,
    unitaryEquivalent_coordinateRepresentation_of_isNonzero_fiberRestriction
      H rho hrho i hi⟩

/-- The coordinate in the preceding classification is unique. -/
theorem existsUnique_coordinate_unitaryEquivalent {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) :
    ∃! i : ι, (coordinateRepresentation H i).UnitaryEquivalent rho := by
  obtain ⟨i, hi⟩ := exists_coordinate_unitaryEquivalent H rho hrho
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hij : (coordinateRepresentation H j).UnitaryEquivalent
      (coordinateRepresentation H i) := hj.trans hi.symm
  exact not_unitaryEquivalent_coordinateRepresentation_of_ne H hji hij

/-- Strong form: the unique coordinate is simultaneously the unique active
restriction and the coordinate giving the actual unitary equivalence. -/
theorem existsUnique_active_coordinate {K : Type uK}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) :
    ∃! i : ι,
      (fiberRestriction H rho i).IsNonzero ∧
        (coordinateRepresentation H i).UnitaryEquivalent rho := by
  obtain ⟨i, hi, huniq⟩ := C0DirectSum.existsUnique_isNonzero_comp_single
    (fun j => ClassificationFiber H j) rho hrho
  refine ⟨i, ⟨hi,
    unitaryEquivalent_coordinateRepresentation_of_isNonzero_fiberRestriction
      H rho hrho i hi⟩, ?_⟩
  intro j hj
  exact huniq j hj.1

/-- The c₀-sum is CCR in the representation-side sense: every nonzero
irreducible representation has literal compact-operator range. -/
theorem range_eq_compactOperatorStarSubalgebra_of_isIrreducible
    {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K)
    (hrho : rho.IsIrreducible) :
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  obtain ⟨i, hi⟩ := exists_coordinate_unitaryEquivalent H rho hrho
  exact hi.range_eq_compactOperatorStarSubalgebra (range_coordinateRepresentation H i)

/-- Universally quantified CCR endpoint for the dependent compact-operator c₀
sum, with no separability assumption on the index or fibres. -/
theorem forall_irreducible_range_eq_compactOperatorStarSubalgebra :
    ∀ (K : Type uK) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
      ∀ rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K,
        rho.IsIrreducible →
          (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  intro K _ _ _ rho hrho
  exact range_eq_compactOperatorStarSubalgebra_of_isIrreducible H rho hrho

end CompactOperatorC0Sum

end MathlibAnnex.Analysis.CStarAlgebra
