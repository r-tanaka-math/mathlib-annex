/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Kadison
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-!
# The bounded transform in a genuinely nonunital algebra

The already defined scalar function `boundedSelfAdjointScalar` vanishes at
zero. Its nonunital functional calculus therefore belongs to the original
algebra and has norm at most one there, independently of representation
faithfulness. After representation, it is the unital bounded transform, so
the existing two-resolvent error estimate applies without a lifting axiom.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The bounded transform is admissible for nonunital functional calculus. -/
theorem boundedSelfAdjointScalar_zero : boundedSelfAdjointScalar 0 = 0 := by
  simp [boundedSelfAdjointScalar]

/-- The transformed element is self-adjoint in the original algebra. -/
theorem isSelfAdjoint_cfcₙ_boundedSelfAdjointScalar (a : A) :
    IsSelfAdjoint (cfcₙ boundedSelfAdjointScalar a) :=
  cfcₙ_predicate (p := IsSelfAdjoint) boundedSelfAdjointScalar a

/-- The bound is on the source element, not only on its represented image. -/
theorem norm_cfcₙ_boundedSelfAdjointScalar_le_one (a : A) :
    ‖cfcₙ boundedSelfAdjointScalar a‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  simpa [Real.norm_eq_abs] using abs_boundedSelfAdjointScalar_le_one t

/-- Naturality identifies the original-algebra transform with the existing
operator transform used in the resolvent error estimates. -/
theorem NonUnitalCStarRepresentation.map_cfcₙ_boundedSelfAdjointScalar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : IsSelfAdjoint a) :
    pi (cfcₙ boundedSelfAdjointScalar a) = boundedSelfAdjointTransform (pi a) := by
  rw [pi.map_cfcₙ boundedSelfAdjointScalar a
    continuous_boundedSelfAdjointScalar.continuousOn boundedSelfAdjointScalar_zero
    (by fun_prop) ha (ha.map pi)]
  exact cfcₙ_eq_cfc continuous_boundedSelfAdjointScalar.continuousOn
    boundedSelfAdjointScalar_zero

end MathlibAnnex.Analysis.CStarAlgebra
