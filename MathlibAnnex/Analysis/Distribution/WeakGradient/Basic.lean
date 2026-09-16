import MathlibAnnex.Analysis.Distribution.Divergence
import MathlibAnnex.MeasureTheory.Function.AEConstant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open Set MeasureTheory
namespace MathlibAnnex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

/-- Vanishing weak gradient, tested by compact C¹ vector fields on a
finite-dimensional real normed space.  The finite-dimensional instance is part
of the public declaration type.  Local integrability remains a separate
required hypothesis of the rigidity theorem; this integral equation alone is
not a substitute for local integrability. -/
def WeakDivergenceZero [FiniteDimensional ℝ E]
    (μ : Measure E) (U : Set E) (u : E → ℝ) : Prop :=
  ∀ W : CompactC1VectorField E, W.carrier ⊆ U →
    ∫ y in U, u y * divergence W y ∂μ = 0

end MathlibAnnex
