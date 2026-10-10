/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Rank-one operators in the concrete compact-operator algebra

The existing rank-one operator is bundled in the existing compact subtype.
Evaluation, linearity in the output slot, star and multiplication are retained
for real/complex Hilbert spaces. There is no representation or GSS hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Set InnerProductSpace
open scoped InnerProduct

namespace InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The existing rank-one operator in the existing compact-operator subtype. -/
def compactRankOne (𝕜 : Type*) [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (x y : H) : ContinuousLinearMap.compactOperatorStarSubalgebra 𝕜 H :=
  ⟨rankOne 𝕜 x y, isCompactOperator_rankOne x y⟩

@[simp]
theorem coe_compactRankOne (x y : H) :
    (compactRankOne 𝕜 x y : H →L[𝕜] H) = rankOne 𝕜 x y := rfl

@[simp]
theorem compactRankOne_apply (x y z : H) :
    (compactRankOne 𝕜 x y : H →L[𝕜] H) z = inner 𝕜 y z • x := rfl

/-- Addition in the output slot, in the actual compact subtype. -/
theorem compactRankOne_add_left (x x' y : H) :
    compactRankOne 𝕜 (x + x') y = compactRankOne 𝕜 x y + compactRankOne 𝕜 x' y := by
  apply Subtype.ext
  ext z
  change inner 𝕜 y z • (x + x') = inner 𝕜 y z • x + inner 𝕜 y z • x'
  exact smul_add _ _ _

/-- The first rank-one slot is linear, not conjugate-linear. -/
theorem compactRankOne_smul_left (c : 𝕜) (x y : H) :
    compactRankOne 𝕜 (c • x) y = c • compactRankOne 𝕜 x y := by
  apply Subtype.ext
  ext z
  change inner 𝕜 y z • (c • x) = c • (inner 𝕜 y z • x)
  exact smul_comm _ _ _

@[simp]
theorem star_compactRankOne (x y : H) :
    star (compactRankOne 𝕜 x y) = compactRankOne 𝕜 y x := by
  apply Subtype.ext
  change star (rankOne 𝕜 x y) = rankOne 𝕜 y x
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- Rank-one multiplication with the original inner-product slots. -/
theorem compactRankOne_mul (x y z w : H) :
    compactRankOne 𝕜 x y * compactRankOne 𝕜 z w =
      inner 𝕜 y z • compactRankOne 𝕜 x w := by
  apply Subtype.ext
  exact rankOne_comp_rankOne x y z w

/-- Multiplication by a compact operator acts on the output vector. -/
theorem mul_compactRankOne (a : ContinuousLinearMap.compactOperatorStarSubalgebra 𝕜 H)
    (x y : H) :
    a * compactRankOne 𝕜 x y = compactRankOne 𝕜 ((a : H →L[𝕜] H) x) y := by
  apply Subtype.ext
  exact comp_rankOne x y (a : H →L[𝕜] H)

end InnerProductSpace

