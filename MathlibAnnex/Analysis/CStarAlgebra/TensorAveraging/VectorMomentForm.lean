import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRankBridge
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorForms
import MathlibAnnex.Analysis.Normed.TensorProduct.BidualForms

/-!
# Vector moments as projective-tensor bilinear forms

The vector-moment tests in the finite-row bridge are exactly the restricted
vector-product bilinear forms under the project's fixed completed projective
tensor duality.  The existing Hilbert factorization proves their Arens
regularity.  This special case does not establish weak compactness for an
arbitrary bounded C-star bilinear form (the BIL Work target).
-/

set_option autoImplicit false
open scoped CStarAlgebra InnerProductSpace
noncomputable section

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tensorDual_matrixCoefficient_eq_vectorProductForm
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    tensorDualIsometry (matrixCoefficient A H ρ η ξ) =
      MathlibAnnex.CStarAlgebra.VectorForms.vectorProductForm ρ η ξ := by
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [tensorDualIsometry_apply,
      MathlibAnnex.CStarAlgebra.VectorForms.vectorProductForm_apply,
      matrixCoefficient_apply, representedProduct_tprod]
  rw [map_mul]
  rfl

theorem tensorDual_vectorMoment_eq_vectorProductForm
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    tensorDualIsometry (vectorMoment A H ρ ξ) =
      MathlibAnnex.CStarAlgebra.VectorForms.vectorProductForm ρ ξ ξ := by
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [tensorDualIsometry_apply,
      MathlibAnnex.CStarAlgebra.VectorForms.vectorProductForm_apply,
      vectorMoment_apply, representedProduct_tprod]
  change inner ℂ ξ (ρ (a * b) ξ) = inner ℂ ξ (ρ a (ρ b ξ))
  rw [map_mul]
  rfl

theorem isArensRegular_matrixCoefficient
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    MathlibAnnex.ProjectiveTensorProduct.IsArensRegular
      (matrixCoefficient A H ρ η ξ) := by
  change MathlibAnnex.WeakCompact.IsWeaklyCompact
    (tensorDualIsometry (matrixCoefficient A H ρ η ξ))
  rw [tensorDual_matrixCoefficient_eq_vectorProductForm A H ρ η ξ]
  exact MathlibAnnex.CStarAlgebra.VectorForms.isWeaklyCompact_vectorProductForm ρ η ξ

theorem matrixCoefficient_exists_normal_extension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    ∃ C : MathlibAnnex.BidualBilinear.BidualForm ℂ A A,
      MathlibAnnex.BidualBilinear.SeparatelyWeakStarContinuous C ∧
      MathlibAnnex.BidualBilinear.Extends
        (tensorDualIsometry (matrixCoefficient A H ρ η ξ)) C ∧
      ‖C‖ = ‖matrixCoefficient A H ρ η ξ‖ :=
  (MathlibAnnex.ProjectiveTensorProduct.isArensRegular_iff_exists_extension
    (matrixCoefficient A H ρ η ξ)).mp
      (isArensRegular_matrixCoefficient A H ρ η ξ)

theorem isArensRegular_vectorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    MathlibAnnex.ProjectiveTensorProduct.IsArensRegular
      (vectorMoment A H ρ ξ) := by
  change MathlibAnnex.WeakCompact.IsWeaklyCompact
    (tensorDualIsometry (vectorMoment A H ρ ξ))
  rw [tensorDual_vectorMoment_eq_vectorProductForm A H ρ ξ]
  exact MathlibAnnex.CStarAlgebra.VectorForms.isWeaklyCompact_vectorProductForm ρ ξ ξ

/-- The canonical bidual extension exists for this particular vector-moment
test.  Its conclusion is not quantified over arbitrary tensor-dual `f`. -/
theorem vectorMoment_exists_normal_extension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ∃ C : MathlibAnnex.BidualBilinear.BidualForm ℂ A A,
      MathlibAnnex.BidualBilinear.SeparatelyWeakStarContinuous C ∧
      MathlibAnnex.BidualBilinear.Extends
        (tensorDualIsometry (vectorMoment A H ρ ξ)) C ∧
      ‖C‖ = ‖vectorMoment A H ρ ξ‖ :=
  (MathlibAnnex.ProjectiveTensorProduct.isArensRegular_iff_exists_extension
    (vectorMoment A H ρ ξ)).mp
      (isArensRegular_vectorMoment A H ρ ξ)

end MathlibAnnex.CStarAlgebra.TensorAveraging
