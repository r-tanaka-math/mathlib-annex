import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.OmegaFromMean

/-!
# The represented vector moment of an averaged tensor functional

This identifies the precise multiplication-form extension identity needed
for one vector in the same representation used by `FiniteRankBridge`.
The extension and normalized mean remain explicit inputs; neither exists
by virtue of this lemma.
-/

set_option autoImplicit false
open scoped CStarAlgebra InnerProductSpace BoundedContinuousFunction
noncomputable section

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H]
  [CompleteSpace H]

/-- The vector coefficient functional on the represented operator algebra. -/
def operatorVectorState (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

/-- General represented matrix coefficient, linear in the operator. -/
def operatorMatrixCoefficient (η ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ η).comp (ContinuousLinearMap.apply ℂ H ξ)

theorem operatorMatrixCoefficient_one (η ξ : H) :
    operatorMatrixCoefficient H η ξ 1 = inner ℂ η ξ := by
  simp [operatorMatrixCoefficient]

theorem operatorVectorState_one (ξ : H) :
    operatorVectorState H ξ 1 = (‖ξ‖ ^ 2 : ℂ) := by
  simp [operatorVectorState, inner_self_eq_norm_sq_to_K]

/-- Off-diagonal matrix coefficients retain both vectors in the same
representation through the sampled multiplication moment. -/
theorem fromMean_matrixCoefficient
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm (H →L[ℂ] H))
    (m : (Isometry (H →L[ℂ] H) →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry (H →L[ℂ] H)) 1) = 1)
    (η ξ : H)
    (hExt : E (matrixCoefficient A H ρ η ξ) =
      mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ)) :
    fromMean A (H →L[ℂ] H) E m (matrixCoefficient A H ρ η ξ) =
      inner ℂ η ξ := by
  rw [fromMean_mulForm A (H →L[ℂ] H) E m hone
    (matrixCoefficient A H ρ η ξ) (operatorMatrixCoefficient H η ξ) hExt]
  exact operatorMatrixCoefficient_one H η ξ

/-- Off-diagonal extension identities for one fixed right vector identify
the entire represented-vector bidual action on that vector.  This is the
exact rank-one input used by the finite-row approximation map. -/
theorem fromMean_representedVector
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm (H →L[ℂ] H))
    (m : (Isometry (H →L[ℂ] H) →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry (H →L[ℂ] H)) 1) = 1)
    (ξ : H)
    (hExt : ∀ η : H,
      E (matrixCoefficient A H ρ η ξ) =
        mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ))
    (g : StrongDual ℂ H) :
    fromMean A (H →L[ℂ] H) E m
      (g.comp (representedVector A H ρ ξ)) = g ξ := by
  let η : H := (InnerProductSpace.toDual ℂ H).symm g
  have hg : g = innerSL ℂ η := by
    apply ContinuousLinearMap.ext
    intro v
    simpa [η] using (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := v) (y := g))
  rw [hg]
  exact fromMean_matrixCoefficient A H ρ E m hone η ξ (hExt η)

/-- A genuine extension identity for the original vector-moment test is
enough for the Ω moment equation, with no change of representation or vector. -/
theorem fromMean_vectorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm (H →L[ℂ] H))
    (m : (Isometry (H →L[ℂ] H) →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry (H →L[ℂ] H)) 1) = 1)
    (ξ : H)
    (hExt : E (vectorMoment A H ρ ξ) =
      mulForm (H →L[ℂ] H) (operatorVectorState H ξ)) :
    fromMean A (H →L[ℂ] H) E m (vectorMoment A H ρ ξ) =
      (‖ξ‖ ^ 2 : ℂ) := by
  rw [fromMean_mulForm A (H →L[ℂ] H) E m hone
    (vectorMoment A H ρ ξ) (operatorVectorState H ξ) hExt]
  exact operatorVectorState_one H ξ

end MathlibAnnex.CStarAlgebra.TensorAveraging
