import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Kernel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix coefficients under composition and adjoints

The adjoint exchanges the coefficient vectors and conjugates the value.
The two-sided identity below records the adjoint on the correct side of a
spatial transformation; it does not assume a classification of such transformations.
-/

set_option autoImplicit false

noncomputable section

namespace InnerProductSpace

variable {𝕜 E F K L : Type*} [RCLike 𝕜]
section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [SeminormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable [SeminormedAddCommGroup L] [InnerProductSpace 𝕜 L]

theorem matrixCoefficient_apply_comp (U : E →L[𝕜] K) (T : K →L[𝕜] F)
    (x : E) (y : F) :
    matrixCoefficient 𝕜 x y (T.comp U) = matrixCoefficient 𝕜 (U x) y T := rfl

/-- Transport by linear isometric equivalences does not require completeness. -/
theorem matrixCoefficient_apply_conjugate
    (U : E ≃ₗᵢ[𝕜] K) (V : F ≃ₗᵢ[𝕜] L) (T : E →L[𝕜] F) (x : E) (y : F) :
    matrixCoefficient 𝕜 (U x) (V y)
      (V.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      matrixCoefficient 𝕜 x y T := by
  change inner 𝕜 (V y) (V (T (U.symm (U x)))) = inner 𝕜 y (T x)
  rw [U.symm_apply_apply, V.inner_map_map]

theorem conjugate_mem_ker_matrixCoefficient_iff
    (U : E ≃ₗᵢ[𝕜] K) (V : F ≃ₗᵢ[𝕜] L) (T : E →L[𝕜] F) (x : E) (y : F) :
    V.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∈
      (matrixCoefficient 𝕜 (U x) (V y)).ker ↔ T ∈ (matrixCoefficient 𝕜 x y).ker := by
  change matrixCoefficient 𝕜 (U x) (V y) _ = 0 ↔ matrixCoefficient 𝕜 x y T = 0
  rw [matrixCoefficient_apply_conjugate]

end Seminormed

section Adjoint

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Complex conjugation is essential here. -/
theorem matrixCoefficient_apply_adjoint (T : E →L[𝕜] F) (x : E) (y : F) :
    matrixCoefficient 𝕜 y x (ContinuousLinearMap.adjoint T) =
      star (matrixCoefficient 𝕜 x y T) := by
  simp only [matrixCoefficient_apply, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := 𝕜) (T x) y).symm

theorem adjoint_mem_ker_matrixCoefficient_iff (T : E →L[𝕜] F) (x : E) (y : F) :
    ContinuousLinearMap.adjoint T ∈ (matrixCoefficient 𝕜 y x).ker ↔
      T ∈ (matrixCoefficient 𝕜 x y).ker := by
  change matrixCoefficient 𝕜 y x (ContinuousLinearMap.adjoint T) = 0 ↔
    matrixCoefficient 𝕜 x y T = 0
  rw [matrixCoefficient_apply_adjoint, star_eq_zero]

end Adjoint

section TwoSided

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- Pulling back the two coefficient vectors corresponds to `V† T U`.
Only the spaces needed for the adjoint of `V` are assumed complete. -/
theorem matrixCoefficient_apply_adjoint_comp_comp
    (U : E →L[𝕜] K) (V : F →L[𝕜] L) (T : K →L[𝕜] L) (x : E) (y : F) :
    matrixCoefficient 𝕜 x y ((ContinuousLinearMap.adjoint V).comp (T.comp U)) =
      matrixCoefficient 𝕜 (U x) (V y) T := by
  change inner 𝕜 y (ContinuousLinearMap.adjoint V (T (U x))) =
    inner 𝕜 (V y) (T (U x))
  exact ContinuousLinearMap.adjoint_inner_right V y (T (U x))

theorem adjoint_comp_comp_mem_ker_matrixCoefficient_iff
    (U : E →L[𝕜] K) (V : F →L[𝕜] L) (T : K →L[𝕜] L) (x : E) (y : F) :
    (ContinuousLinearMap.adjoint V).comp (T.comp U) ∈ (matrixCoefficient 𝕜 x y).ker ↔
      T ∈ (matrixCoefficient 𝕜 (U x) (V y)).ker := by
  change matrixCoefficient 𝕜 x y _ = 0 ↔ matrixCoefficient 𝕜 (U x) (V y) T = 0
  rw [matrixCoefficient_apply_adjoint_comp_comp]

end TwoSided

end InnerProductSpace
