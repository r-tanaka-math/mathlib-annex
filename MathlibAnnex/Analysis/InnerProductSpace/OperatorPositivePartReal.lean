/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic
import MathlibAnnex.Analysis.InnerProductSpace.RealComplexification

/-!
# Positive and negative parts of a real self-adjoint Hilbert-space operator

The construction uses a genuine complex Hilbert space with the L2 norm on pairs.
Complex conjugation fixes precisely the embedded real space. Conjugating an operator
preserves positivity. Uniqueness of the complex positive/negative decomposition
therefore makes both parts invariant under conjugation; they descend to real operators.
No real continuous-functional-calculus instance is an input or installed here.
The original norm on H and the standard operator norm are unchanged.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate CStarAlgebra

namespace ContinuousLinearMap
open InnerProductSpace RealComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedSpace ℝ (RealComplexification H →L[ℂ] RealComplexification H) :=
  NormedSpace.complexToReal
local instance : Module ℝ (RealComplexification H →L[ℂ] RealComplexification H) :=
  (NormedSpace.complexToReal :
    NormedSpace ℝ (RealComplexification H →L[ℂ] RealComplexification H)).toModule

/-- The positive real part obtained by complexification and descent, with the original norm. -/
def realPositivePart (D : H →L[ℝ] H) : H →L[ℝ] H := descend ((RealComplexification.extend D)⁺)

/-- The corresponding negative real part; no second inner product is put on H. -/
def realNegativePart (D : H →L[ℝ] H) : H →L[ℝ] H := descend ((RealComplexification.extend D)⁻)

/-- Every bounded symmetric real Hilbert operator has actual positive orthogonal parts.
There is no finite-dimensionality, separability or real-CFC hypothesis. -/
theorem realPositivePart_decomposition (D : H →L[ℝ] H) (hD : D.IsSymmetric) :
    (realPositivePart D).IsPositive ∧ (realNegativePart D).IsPositive ∧
      D = realPositivePart D - realNegativePart D ∧
      (realNegativePart D).comp (realPositivePart D) = 0 := by
  have hs : IsSelfAdjoint (RealComplexification.extend D) :=
    isSelfAdjoint_iff_isSymmetric.mpr (isSymmetric_extend D hD)
  obtain ⟨hpfix, hnfix⟩ := conjugateOperator_posPart_negPart
    (RealComplexification.extend D) hs (conjugateOperator_extend D)
  have hp : ((RealComplexification.extend D)⁺).IsPositive :=
    (nonneg_iff_isPositive _).mp (CFC.posPart_nonneg (RealComplexification.extend D))
  have hn : ((RealComplexification.extend D)⁻).IsPositive :=
    (nonneg_iff_isPositive _).mp (CFC.negPart_nonneg (RealComplexification.extend D))
  refine ⟨isPositive_descend hpfix hp, isPositive_descend hnfix hn, ?_, ?_⟩
  · have hh := congrArg descend (CFC.posPart_sub_negPart (RealComplexification.extend D) hs)
    simpa only [descend_sub, descend_extend, realPositivePart, realNegativePart] using hh.symm
  · change descend ((RealComplexification.extend D)⁻) * descend ((RealComplexification.extend D)⁺) = 0
    rw [← descend_mul _ _ hpfix, CFC.negPart_mul_posPart, descend_zero]

end ContinuousLinearMap
