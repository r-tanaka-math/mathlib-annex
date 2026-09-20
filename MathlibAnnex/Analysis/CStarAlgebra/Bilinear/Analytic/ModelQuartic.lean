import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.QuarticImaginary
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.NormalizedSequenceForm

/-!
# Applying the new analytic bound to the retained C01 normalized model

The sequence order instances are local copies of the same spectral-order
choices used in C01.  The C*-matrix norm and its spectral-order instances
are Mathlib's existing ones.  No shared bidual instance is introduced.

The input variables here really are selfadjoint elements of the normalized
matrix algebras.  The maps `leftInput` and `rightInput` are NOT falsely
asserted to preserve selfadjointness; the later general-element reduction
must still be supplied before this yields a row/column estimate for B.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.NormalizedSequenceBilinear

open MathlibAnnex.MatrixContraction
open MathlibAnnex.CStarBilinear.Analytic

universe u v
local instance a1SequenceOrder (X : Type*) [CStarAlgebra X] :
    PartialOrder (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrder _
local instance a1SequenceStarOrder (X : Type*) [CStarAlgebra X] :
    StarOrderedRing (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrderedRing _
local instance modelSequenceNontrivial (X : Type*) [CStarAlgebra X] [Nontrivial X] :
    Nontrivial (BoundedContinuousFunction ℕ X) := by
  refine ⟨constants X 0, constants X 1, ?_⟩
  intro h
  exact zero_ne_one (congrArg (fun f : BoundedContinuousFunction ℕ X => f 0) h)
local instance modelMatrixNontrivial (X : Type*) [CStarAlgebra X] [Nontrivial X] :
    Nontrivial (TwoByTwo (BoundedContinuousFunction ℕ X)) := by
  refine ⟨0, 1, ?_⟩
  intro h
  have h00 := congrArg (fun M : TwoByTwo (BoundedContinuousFunction ℕ X) => M 0 0) h
  exact (zero_ne_one : (0 : BoundedContinuousFunction ℕ X) ≠ 1) (by simpa using h00)

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {D : Type v} [CStarAlgebra D] [Nontrivial D]

/-- Actual application to the previously constructed normalized model,
with no analytic supplier assumption. -/
theorem model_abs_im_quartic_le (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0)
    (x : TwoByTwo (BoundedContinuousFunction ℕ A)) (hx : IsSelfAdjoint x)
    (y : TwoByTwo (BoundedContinuousFunction ℕ D)) (hy : IsSelfAdjoint y) :
    |(model B x y).im| ≤
      36 * fourthRoot (fourthMoment (leftMarginal (model B)) x) *
        fourthRoot (fourthMoment (rightMarginal (model B)) y) :=
  normalized_abs_im_quartic_le (model B) (model_norm B hB).le (model_one B hB)
    x hx y hy

end MathlibAnnex.NormalizedSequenceBilinear
