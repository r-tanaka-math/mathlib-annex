/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment
import MathlibAnnex.Analysis.Normed.GeometricStructure.ExposedFace

/-!
# Attaining coefficient slices and the shared supporting-functional interface

The coefficient slice uses the shared `NormedSpace.unitBallSupportFace`,
together with `NormedSpace.supportFunctionals` and `NormedSpace.supportKernelUnion`.
This is the same value-one slice, with the ball-membership conjunct first.

The results here give nonemptiness, one actual supporting functional, and kernel
inclusion. They do not assert that the supporting family is a singleton, that the
slice is maximal, or that its kernel belongs to the geometric structure space.
Those conclusions require the later extreme-functional and maximal-face proofs.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra
namespace NonUnitalCStarRepresentation

variable {A H : Type*} [NonUnitalCStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unit-vector coefficient supports its value-one slice of the closed unit ball.
No nonemptiness or irreducibility is asserted in this statement. -/
theorem matrixCoefficient_mem_supportFunctionals_unitBallSupportFace
    (pi : NonUnitalCStarRepresentation A H) (xi eta : H)
    (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    matrixCoefficient pi xi eta ∈ NormedSpace.supportFunctionals ℂ
      (NormedSpace.unitBallSupportFace ℂ (matrixCoefficient pi xi eta)) := by
  apply (NormedSpace.mem_supportFunctionals ℂ _ _).2
  refine ⟨?_, ?_⟩
  · simpa only [hxi, heta, one_mul] using norm_matrixCoefficient_le pi xi eta
  · intro a ha
    exact ha.2

/-- Irreducibility makes the coefficient's value-one slice nonempty, with an actual
norm-one witness from the original nonunital algebra. -/
theorem nonempty_unitBallSupportFace_matrixCoefficient_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    (NormedSpace.unitBallSupportFace ℂ (matrixCoefficient pi xi eta)).Nonempty := by
  obtain ⟨a, ha, hvalue⟩ :=
    exists_norm_eq_one_matrixCoefficient_eq_one_of_isIrreducible pi hpi xi eta hxi heta
  exact ⟨a, mem_closedBall_zero_iff.mpr ha.le, hvalue⟩

/-- One inclusion in the desired kernel identification. Equality is not obtained
without the singleton theorem for the entire supporting family. -/
theorem ker_matrixCoefficient_subset_supportKernelUnion
    (pi : NonUnitalCStarRepresentation A H) (xi eta : H)
    (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    ((matrixCoefficient pi xi eta).ker : Set A) ⊆ NormedSpace.supportKernelUnion ℂ
      (NormedSpace.unitBallSupportFace ℂ (matrixCoefficient pi xi eta)) := by
  intro a ha
  exact ⟨matrixCoefficient pi xi eta,
    matrixCoefficient_mem_supportFunctionals_unitBallSupportFace pi xi eta hxi heta,
    ha⟩

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
