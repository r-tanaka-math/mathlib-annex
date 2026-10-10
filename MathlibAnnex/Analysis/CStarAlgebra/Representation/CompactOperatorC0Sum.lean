/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel

/-!
# Coordinate representations of c₀-sums of compact-operator algebras

Each coordinate evaluation is a surjective nonunital star homomorphism.  Pulling
back the concrete compact-operator representation therefore gives a nonzero
irreducible representation of the dependent c₀-direct sum.  Its kernel is
computed exactly by vanishing of that coordinate, and distinct coordinates have
distinct primitive kernels.

This file does not yet assert that every irreducible representation of the c₀
sum is a coordinate representation; that classification is the next independent
proof obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uH

namespace CompactOperatorC0Sum

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]

private abbrev Fibre (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

/-- Evaluation of a compact-operator c₀-family at one coordinate. -/
def coordinateEvaluation (i : ι) : CompactOperatorC0Sum H →⋆ₙₐ[ℂ] Fibre H i :=
  C0DirectSum.eval (fun j => Fibre H j) i

@[simp]
theorem coordinateEvaluation_apply (i : ι) (x : CompactOperatorC0Sum H) :
    coordinateEvaluation H i x = x.1 i := rfl

/-- The concrete action of the `i`-th compact-operator fibre. -/
def coordinateRepresentation (i : ι) :
    NonUnitalCStarRepresentation (CompactOperatorC0Sum H) (H i) :=
  (compactOperatorRepresentation (H i)).comp (coordinateEvaluation H i)

@[simp]
theorem coordinateRepresentation_apply (i : ι) (x : CompactOperatorC0Sum H) (v : H i) :
    coordinateRepresentation H i x v = (x.1 i : H i →L[ℂ] H i) v := rfl

/-- Coordinate evaluation is surjective, witnessed by the actual single-coordinate
c₀ embedding. -/
theorem coordinateEvaluation_surjective (i : ι) :
    Function.Surjective (coordinateEvaluation H i) :=
  C0DirectSum.eval_surjective (fun j => Fibre H j) i

/-- Every coordinate representation is nonzero. -/
theorem isNonzero_coordinateRepresentation (i : ι) :
    (coordinateRepresentation H i).IsNonzero := by
  exact (NonUnitalCStarRepresentation.isNonzero_comp_iff_of_surjective
    (compactOperatorRepresentation (H i)) (coordinateEvaluation H i)
    (coordinateEvaluation_surjective H i)).2
      ((isNonzero_compactOperatorRepresentation_iff (H i)).2 inferInstance)

/-- Every coordinate representation is irreducible. -/
theorem isIrreducible_coordinateRepresentation (i : ι) :
    (coordinateRepresentation H i).IsIrreducible := by
  exact (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
    (compactOperatorRepresentation (H i)) (coordinateEvaluation H i)
    (coordinateEvaluation_surjective H i)).2
      (isIrreducible_compactOperatorRepresentation (H i))

/-- The coordinate kernel is exactly the set of c₀-families whose `i`-th
coordinate vanishes. -/
@[simp]
theorem coordinateRepresentation_eq_zero_iff (i : ι) (x : CompactOperatorC0Sum H) :
    coordinateRepresentation H i x = 0 ↔ coordinateEvaluation H i x = 0 := by
  constructor
  · intro hzero
    apply compactOperatorRepresentation_injective (H i)
    simpa [coordinateRepresentation] using hzero
  · intro hzero
    simp [coordinateRepresentation, hzero]

/-- Exact membership formula for the primitive ideal of a coordinate
representation. -/
@[simp]
theorem mem_coordinateKernel (i : ι) (x : CompactOperatorC0Sum H) :
    x ∈ NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H i) ↔
      coordinateEvaluation H i x = 0 := by
  exact (NonUnitalCStarRepresentation.mem_kernelIdeal (coordinateRepresentation H i) x).trans
    (coordinateRepresentation_eq_zero_iff H i x)

/-- A single-coordinate compact operator is represented at that coordinate by
its concrete action. -/
@[simp]
theorem coordinateRepresentation_single_same (i : ι) (a : Fibre H i) :
    coordinateRepresentation H i
        (C0DirectSum.single (fun j => Fibre H j) i a) =
      compactOperatorRepresentation (H i) a := by
  change compactOperatorRepresentation (H i)
      (C0DirectSum.eval (fun j => Fibre H j) i
        (C0DirectSum.single (fun j => Fibre H j) i a)) = _
  rw [C0DirectSum.eval_single_same]

/-- A single-coordinate compact operator is annihilated at every other
coordinate. -/
@[simp]
theorem coordinateRepresentation_single_of_ne {i j : ι} (h : j ≠ i)
    (a : Fibre H i) :
    coordinateRepresentation H j
        (C0DirectSum.single (fun k => Fibre H k) i a) = 0 := by
  change compactOperatorRepresentation (H j)
    (C0DirectSum.eval (fun k => Fibre H k) j
      (C0DirectSum.single (fun k => Fibre H k) i a)) = 0
  rw [C0DirectSum.eval_single_of_ne _ h, map_zero]

/-- Distinct coordinates define distinct primitive kernels. -/
theorem coordinateKernel_ne_of_ne {i j : ι} (hij : i ≠ j) :
    NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H i) ≠
      NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H j) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : H i)
  let a : Fibre H i :=
    ⟨rankOne ℂ v v, isCompactOperator_rankOne v v⟩
  let x : CompactOperatorC0Sum H :=
    C0DirectSum.single (fun k => Fibre H k) i a
  intro heq
  have hxj : x ∈ NonUnitalCStarRepresentation.kernelIdeal
      (coordinateRepresentation H j) := by
    apply (mem_coordinateKernel H j x).2
    change C0DirectSum.eval (fun k => Fibre H k) j
      (C0DirectSum.single (fun k => Fibre H k) i a) = 0
    exact C0DirectSum.eval_single_of_ne (fun k => Fibre H k) hij.symm a
  have hxi : x ∉ NonUnitalCStarRepresentation.kernelIdeal
      (coordinateRepresentation H i) := by
    rw [mem_coordinateKernel]
    simp only [coordinateEvaluation, x, C0DirectSum.eval_single_same]
    intro ha
    apply rankOne_ne_zero (𝕜 := ℂ) hv hv
    exact congrArg Subtype.val ha
  rw [heq] at hxi
  exact hxi hxj

/-- Coordinate representations at distinct indices are not unitarily
equivalent. -/
theorem not_unitaryEquivalent_coordinateRepresentation_of_ne {i j : ι} (hij : i ≠ j) :
    ¬ (coordinateRepresentation H i).UnitaryEquivalent (coordinateRepresentation H j) := by
  intro hU
  apply coordinateKernel_ne_of_ne H hij
  exact hU.kernelIdeal_eq

end CompactOperatorC0Sum

end MathlibAnnex.Analysis.CStarAlgebra
