import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.MeanSampling
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRankBridge

/-!
# Projective-tensor bidual functional from a represented mean

This composes a bounded-linear extension assignment with the proved
isometry-sampling contraction and a bounded mean.  The result really has
the project's completed projective-tensor bidual type.  Neither the
extension assignment nor an invariant mean is constructed in this file.
The multiplication-moment lemma records the exact extra extension identity
needed for represented vector moments.
-/

set_option autoImplicit false
open scoped CStarAlgebra BoundedContinuousFunction
noncomputable section
namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (M : Type*) [CStarAlgebra M] [Nontrivial M]

/-- A bounded-linear extension and bounded mean yield an actual bidual
functional; this is only an assembly map until both inputs are supplied. -/
def fromMean
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm M)
    (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ) :
    StrongDual ℂ (StrongDual ℂ (Tensor A)) :=
  m.comp ((sampleCLM M).comp E)

theorem fromMean_apply
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm M)
    (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (f : StrongDual ℂ (Tensor A)) :
    fromMean A M E m f = m (sample M (E f)) := rfl

theorem fromMean_mulForm
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm M)
    (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry M) 1) = 1)
    (f : StrongDual ℂ (Tensor A)) (φ : M →L[ℂ] ℂ)
    (hf : E f = mulForm M φ) :
    fromMean A M E m f = φ 1 := by
  rw [fromMean_apply, hf]
  exact mean_sample_mulForm M m hone φ

end MathlibAnnex.CStarAlgebra.TensorAveraging
