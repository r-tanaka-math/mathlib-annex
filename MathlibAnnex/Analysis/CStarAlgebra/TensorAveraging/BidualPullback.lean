import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.TensorDual

/-!
# Bounded pullback of the canonical bilinear bidual extension

The received Arens isometry can be transported along a bounded linear map
from a concrete represented space into the fixed bidual model.  This builds
the bounded-linear extension assignment needed by `fromMean` *when such a
concrete corner map is actually supplied*.  Existence of that map, its
multiplicative/central-support properties, and a mean remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.BidualBilinear
open MathlibAnnex.ProjectiveTensorProduct

variable {A M : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup M] [NormedSpace ℂ M]

private def pullbackLinear (j : M →L[ℂ] BidualModel ℂ A) :
    BidualForm ℂ A A →ₗ[ℂ] (M →L[ℂ] M →L[ℂ] ℂ) where
  toFun B := precompRight (B.comp j) j
  map_add' B C := by ext x y; rfl
  map_smul' c B := by ext x y; rfl

private theorem norm_pullback_le
    (j : M →L[ℂ] BidualModel ℂ A) (B : BidualForm ℂ A A) :
    ‖precompRight (B.comp j) j‖ ≤ ‖j‖ ^ 2 * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg B)) (norm_nonneg x))
    fun y => ?_
  change ‖B (j x) (j y)‖ ≤ (‖j‖ ^ 2 * ‖B‖ * ‖x‖) * ‖y‖
  calc
    ‖B (j x) (j y)‖ ≤ ‖B (j x)‖ * ‖j y‖ := (B (j x)).le_opNorm (j y)
    _ ≤ (‖B‖ * ‖j x‖) * (‖j‖ * ‖y‖) :=
      mul_le_mul (B.le_opNorm (j x)) (j.le_opNorm y)
        (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg _))
    _ ≤ (‖B‖ * (‖j‖ * ‖x‖)) * (‖j‖ * ‖y‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (j.le_opNorm x) (norm_nonneg B))
        (mul_nonneg (norm_nonneg j) (norm_nonneg y))
    _ = (‖j‖ ^ 2 * ‖B‖ * ‖x‖) * ‖y‖ := by ring

/-- Pullback of a bidual bilinear form along the same bounded map in both
variables, bundled continuously and linearly in the form. -/
def bilinearPullback (j : M →L[ℂ] BidualModel ℂ A) :
    BidualForm ℂ A A →L[ℂ] (M →L[ℂ] M →L[ℂ] ℂ) := by
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := BidualForm ℂ A A) (F := M →L[ℂ] M →L[ℂ] ℂ)
    (σ := RingHom.id ℂ) (pullbackLinear j) (‖j‖ ^ 2) ?_
  intro B
  exact norm_pullback_le j B

theorem norm_bilinearPullback_apply_le
    (j : M →L[ℂ] BidualModel ℂ A) (B : BidualForm ℂ A A) :
    ‖bilinearPullback j B‖ ≤ ‖j‖ ^ 2 * ‖B‖ :=
  norm_pullback_le j B

/-- The canonical tensor-dual extension is a *bounded-linear* family of
concrete bilinear forms along an actual corner map `j`. -/
def tensorBidualPullback (j : M →L[ℂ] BidualModel ℂ A) :
    StrongDual ℂ (Tensor A) →L[ℂ] (M →L[ℂ] M →L[ℂ] ℂ) :=
  (bilinearPullback j).comp
    ((firstArensIsometry (𝕜 := ℂ) (E := A) (F := A)).toContinuousLinearMap.comp
      ((tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).toLinearIsometry.toContinuousLinearMap))

theorem tensorBidualPullback_apply
    (j : M →L[ℂ] BidualModel ℂ A)
    (f : StrongDual ℂ (Tensor A)) (x y : M) :
    tensorBidualPullback j f x y =
      firstArens (tensorDualIsometry f) (j x) (j y) := by
  simp [tensorBidualPullback, bilinearPullback, pullbackLinear,
    firstArensIsometry, precompRight_apply]

theorem norm_tensorBidualPullback_apply_le
    (j : M →L[ℂ] BidualModel ℂ A) (f : StrongDual ℂ (Tensor A)) :
    ‖tensorBidualPullback j f‖ ≤ ‖j‖ ^ 2 * ‖f‖ := by
  calc
    ‖tensorBidualPullback j f‖ ≤
        ‖j‖ ^ 2 * ‖firstArens (tensorDualIsometry f)‖ :=
      norm_bilinearPullback_apply_le j _
    _ = ‖j‖ ^ 2 * ‖f‖ := by
      rw [norm_firstArens, (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map]

end MathlibAnnex.CStarAlgebra.TensorAveraging
