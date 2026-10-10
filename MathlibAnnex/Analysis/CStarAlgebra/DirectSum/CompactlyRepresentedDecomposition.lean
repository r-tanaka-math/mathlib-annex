/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Ideal.MinimalIdealFamilyModel
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.OrthogonalIdealCompactModel

/-!
# The canonical compact c₀-decomposition of a compactly represented C-star algebra

A faithful compact-valued representation supplies the canonical family of all
minimal nonzero closed star ideals, norm density of their actual finite sums,
and exact compact models on their chosen cyclic Hilbert spaces. This file
passes these proved data to the existing orthogonal-ideal transport and defines
an actual equivalence from the original algebra to the completed compact c₀-sum.

No density or fiber-model hypothesis is added. The auxiliary spectral order is
fixed to `CStarAlgebra.spectralOrder A`, locally, before selecting any cyclic
fiber. The explicit `letI` in the main declaration's result type fixes this
choice even in a caller's context with a different order instance. The local
attributes below make every subsequent formula use exactly the same order,
`compactModelWitness`, dependent carrier, and compact equivalence. They do not
export a new order instance or introduce an order argument to these declarations.

The forward direction is `A` to `CompactOperatorC0Sum`; the inverse is the
already constructed compact ideal-sum map. Coordinate, single, finite-sum,
norm, and finite reconstruction formulas refer to this one equivalence.
The canonical index may be empty. No unit, nontriviality, countability,
separability, or finite-dimensional assumption is imposed.

This is the forward decomposition theorem. It does not identify a diagonal
block algebra with all compact operators on a Hilbert sum, construct the
converse representation, or establish the other characterizations of compact
C-star algebras.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section

open Set
open scoped BigOperators CStarAlgebra Topology

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The canonical global compact c₀-decomposition supplied by the given
faithful compact representation. The ideal family, its orthogonality and
norm density, and its exact fiber models are all produced from `pi` and
`hpi`; none is an additional premise. The order is fixed locally in the
result type as well as in the defining term. -/
def compactC0Decomposition :
    letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
    A ≃⋆ₐ[ℂ] CompactOperatorC0Sum
      (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  exact ClosedStarIdeal.compactC0SumEquivOfDense
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)
    (fun i => i.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi)

/-- The forward map is the existing ideal decomposition followed by the
specified coordinatewise compact equivalences. -/
theorem compactC0Decomposition_apply (a : A) :
    pi.compactC0Decomposition hpi a =
      C0DirectSum.equiv
        (ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)))
        (fun i : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi))
        (Equiv.refl (MinimalClosedStarIdeal A))
        (fun i => i.compactModelEquiv pi hpi)
        ((ClosedStarIdeal.c0SumEquivOfDense
          (minimalClosedStarIdealFamily (A := A))
          pairwiseOrthogonal_minimalClosedStarIdealFamily
          (dense_finiteSums_minimalClosedStarIdealFamily pi hpi)).symm a) := rfl

/-- The inverse is literally the compact sum homomorphism constructed by
the orthogonal-ideal transport, with the actual canonical family and models. -/
@[simp]
theorem compactC0Decomposition_symm_apply
    (x : CompactOperatorC0Sum
      (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)) :
    (pi.compactC0Decomposition hpi).symm x =
      ClosedStarIdeal.compactC0SumHom
        (minimalClosedStarIdealFamily (A := A))
        pairwiseOrthogonal_minimalClosedStarIdealFamily
        (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)
        (fun i => i.compactModelEquiv pi hpi) x := rfl

/-- Each forward coordinate is the fixed compact model of the corresponding
actual ideal coordinate. The ideal coordinate uses the same density proof
and the same assembly as the defining global equivalence. -/
@[simp]
theorem eval_compactC0Decomposition (a : A) (i : MinimalClosedStarIdeal A) :
    C0DirectSum.eval
      (fun j : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
      (pi.compactC0Decomposition hpi a) =
      i.compactModelEquiv pi hpi
        (C0DirectSum.eval
          (ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A))) i
          ((ClosedStarIdeal.c0SumEquivOfDense
            (minimalClosedStarIdealFamily (A := A))
            pairwiseOrthogonal_minimalClosedStarIdealFamily
            (dense_finiteSums_minimalClosedStarIdealFamily pi hpi)).symm a)) := by
  exact ClosedStarIdeal.eval_compactC0SumEquivOfDense
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi)
    (fun j => j.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi) a i

/-- The inclusion of a displayed ideal is taken to its own single compact
coordinate, using its already fixed exact compact model. -/
@[simp]
theorem compactC0Decomposition_coe (i : MinimalClosedStarIdeal A)
    (a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    pi.compactC0Decomposition hpi (a : A) =
      C0DirectSum.single
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
        (i.compactModelEquiv pi hpi a) := by
  exact ClosedStarIdeal.compactC0SumEquivOfDense_coe
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi)
    (fun j => j.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi) i a

/-- On an ideal element, its own coordinate is its chosen compact model. -/
@[simp]
theorem eval_compactC0Decomposition_coe_same (i : MinimalClosedStarIdeal A)
    (a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    C0DirectSum.eval
      (fun j : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
      (pi.compactC0Decomposition hpi (a : A)) = i.compactModelEquiv pi hpi a := by
  rw [compactC0Decomposition_coe, C0DirectSum.eval_single_same]

/-- Every other coordinate of a displayed ideal element is zero. -/
theorem eval_compactC0Decomposition_coe_of_ne {i j : MinimalClosedStarIdeal A}
    (hji : j ≠ i)
    (a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    C0DirectSum.eval
      (fun k : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (k.CompactModelSpace pi hpi)) j
      (pi.compactC0Decomposition hpi (a : A)) = 0 := by
  rw [compactC0Decomposition_coe, C0DirectSum.eval_single_of_ne _ hji]

/-- The inverse of a single compact coordinate is the actual element of the
corresponding ideal obtained from the inverse of its fixed compact model. -/
@[simp]
theorem compactC0Decomposition_symm_single (i : MinimalClosedStarIdeal A)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) :
    (pi.compactC0Decomposition hpi).symm
      (C0DirectSum.single
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi))
        i T) = ((i.compactModelEquiv pi hpi).symm T : A) := by
  exact ClosedStarIdeal.compactC0SumEquivOfDense_symm_single
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi)
    (fun j => j.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi) i T

/-- Finite ambient ideal sums are sent to their finite compact-coordinate
sums under this same global equivalence. -/
@[simp]
theorem compactC0Decomposition_sum (s : Finset (MinimalClosedStarIdeal A))
    (a : ∀ i, ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    pi.compactC0Decomposition hpi (∑ i ∈ s, (a i : A)) =
      ∑ i ∈ s, C0DirectSum.single
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi))
        i (i.compactModelEquiv pi hpi (a i)) := by
  exact ClosedStarIdeal.compactC0SumEquivOfDense_sum
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi)
    (fun j => j.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi) s a

/-- A finite sum of compact single-coordinate elements reconstructs the
finite sum of their actual ideal preimages. -/
@[simp]
theorem compactC0Decomposition_symm_sum (s : Finset (MinimalClosedStarIdeal A))
    (T : ∀ i : MinimalClosedStarIdeal A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) :
    (pi.compactC0Decomposition hpi).symm
      (∑ i ∈ s, C0DirectSum.single
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi))
        i (T i)) = ∑ i ∈ s, ((i.compactModelEquiv pi hpi).symm (T i) : A) := by
  simp only [map_sum, compactC0Decomposition_symm_single]

/-- Finite truncation followed by the inverse reconstructs an actual finite
sum in the original algebra. -/
@[simp]
theorem compactC0Decomposition_symm_truncate (s : Finset (MinimalClosedStarIdeal A))
    (x : CompactOperatorC0Sum
      (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)) :
    (pi.compactC0Decomposition hpi).symm
      (C0DirectSum.truncate
        (fun i : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) s x) =
      ∑ i ∈ s, ((i.compactModelEquiv pi hpi).symm
        (C0DirectSum.eval
          (fun j : MinimalClosedStarIdeal A =>
            ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi))
          i x) : A) := by
  rw [compactC0Decomposition_symm_apply]
  exact ClosedStarIdeal.compactC0SumHom_truncate
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi)
    (fun j => j.compactModelEquiv pi hpi) s x

/-- The canonical decomposition preserves the original C-star norm. -/
@[simp]
theorem norm_compactC0Decomposition (a : A) :
    ‖pi.compactC0Decomposition hpi a‖ = ‖a‖ := by
  exact ClosedStarIdeal.norm_compactC0SumEquivOfDense
    (minimalClosedStarIdealFamily (A := A))
    pairwiseOrthogonal_minimalClosedStarIdealFamily
    (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)
    (fun i => i.compactModelEquiv pi hpi)
    (dense_finiteSums_minimalClosedStarIdealFamily pi hpi) a

/-- The inverse compact sum preserves the completed c₀ norm. -/
@[simp]
theorem norm_compactC0Decomposition_symm
    (x : CompactOperatorC0Sum
      (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)) :
    ‖(pi.compactC0Decomposition hpi).symm x‖ = ‖x‖ := by
  rw [compactC0Decomposition_symm_apply, ClosedStarIdeal.norm_compactC0SumHom]

/-- The canonical forward equivalence is an isometry. -/
theorem isometry_compactC0Decomposition : Isometry (pi.compactC0Decomposition hpi) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  exact norm_compactC0Decomposition pi hpi

/-- The inverse of the very same canonical equivalence is an isometry. -/
theorem isometry_compactC0Decomposition_symm :
    Isometry (pi.compactC0Decomposition hpi).symm := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  exact norm_compactC0Decomposition_symm pi hpi

/-- The original norm is the supremum of the compact-coordinate norms.
The formula also covers the empty canonical index in the zero algebra. -/
theorem norm_eq_ciSup_norm_eval_compactC0Decomposition (a : A) :
    ‖a‖ = ⨆ i : MinimalClosedStarIdeal A,
      ‖C0DirectSum.eval
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
        (pi.compactC0Decomposition hpi a)‖ := by
  calc
    ‖a‖ = ‖pi.compactC0Decomposition hpi a‖ := (norm_compactC0Decomposition pi hpi a).symm
    _ = _ := C0DirectSum.norm_eq_ciSup _ _

/-- Each displayed compact coordinate is contractive in the ambient norm. -/
theorem norm_eval_compactC0Decomposition_le (a : A) (i : MinimalClosedStarIdeal A) :
    ‖C0DirectSum.eval
      (fun j : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
      (pi.compactC0Decomposition hpi a)‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖pi.compactC0Decomposition hpi a‖ := C0DirectSum.norm_eval_le _ i _
    _ = ‖a‖ := norm_compactC0Decomposition pi hpi a

/-- The error of the finite ideal reconstruction equals the c₀ truncation
error of the same canonical decomposition. -/
theorem norm_sub_sum_compactC0Decomposition_symm_eval
    (a : A) (s : Finset (MinimalClosedStarIdeal A)) :
    ‖a - ∑ i ∈ s, ((i.compactModelEquiv pi hpi).symm
      (C0DirectSum.eval
        (fun j : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
        (pi.compactC0Decomposition hpi a)) : A)‖ =
      ‖pi.compactC0Decomposition hpi a - C0DirectSum.truncate
        (fun i : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) s
        (pi.compactC0Decomposition hpi a)‖ := by
  have hnorm := norm_compactC0Decomposition_symm pi hpi
    (pi.compactC0Decomposition hpi a - C0DirectSum.truncate
      (fun i : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) s
      (pi.compactC0Decomposition hpi a))
  simpa only [map_sub, StarAlgEquiv.symm_apply_apply,
    compactC0Decomposition_symm_truncate] using hnorm

/-- Every element is approximated in norm by the finite reconstruction of
its own canonical compact coordinates, not by independently chosen ideal
approximants. The pre-existing norm density was used to construct the
surjective equivalence; this is a subsequent reconstruction formula. -/
theorem exists_finset_norm_sub_sum_compactC0Decomposition_symm_eval_lt
    (a : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (MinimalClosedStarIdeal A),
      ‖a - ∑ i ∈ s, ((i.compactModelEquiv pi hpi).symm
        (C0DirectSum.eval
          (fun j : MinimalClosedStarIdeal A =>
            ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (j.CompactModelSpace pi hpi)) i
          (pi.compactC0Decomposition hpi a)) : A)‖ < ε := by
  have ht : ∃ s : Finset (MinimalClosedStarIdeal A),
      ‖pi.compactC0Decomposition hpi a - C0DirectSum.truncate
        (fun i : MinimalClosedStarIdeal A =>
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) s
        (pi.compactC0Decomposition hpi a)‖ < ε :=
    @C0DirectSum.exists_finset_norm_sub_truncate_lt
      (MinimalClosedStarIdeal A)
      (fun i : MinimalClosedStarIdeal A =>
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi))
      (fun i => inferInstance)
      (pi.compactC0Decomposition hpi a) ε hε
  obtain ⟨s, hs⟩ := ht
  refine ⟨s, ?_⟩
  rw [norm_sub_sum_compactC0Decomposition_symm_eval]
  exact hs

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
