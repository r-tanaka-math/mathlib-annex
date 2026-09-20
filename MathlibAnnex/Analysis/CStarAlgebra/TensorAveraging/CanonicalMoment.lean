import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorMomentForm
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.TensorDual

/-!
# Canonical bidual extensions of represented vector moments

The represented tensor-dual tests have an actual Arens-regularity proof, so
the received linear isometry supplies their canonical normal extension.  This
does not assert regularity of arbitrary C-star bilinear forms, nor construct a
normal map from a represented envelope to the bidual model.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.BidualBilinear

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The represented vector-moment test, extended canonically and linearly to
the two bidual variables. -/
def canonicalVectorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    BidualForm ℂ A A :=
  (firstArensIsometry (𝕜 := ℂ) (E := A) (F := A))
    ((tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A))
      (vectorMoment A H ρ ξ))

/-- The same canonical construction for an off-diagonal represented matrix
coefficient.  This is a genuine finite-vector test, not a universal W1
supplier for arbitrary bounded bilinear forms. -/
def canonicalMatrixCoefficient
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    BidualForm ℂ A A :=
  (firstArensIsometry (𝕜 := ℂ) (E := A) (F := A))
    ((tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A))
      (matrixCoefficient A H ρ η ξ))

/-- The same extension in the fixed completed-projective tensor dual model. -/
def canonicalVectorTensorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    StrongDual ℂ (Completion ℂ (BidualModel ℂ A) (BidualModel ℂ A)) :=
  (firstExtensionIsometry (𝕜 := ℂ) (E := A) (F := A))
    (vectorMoment A H ρ ξ)

theorem norm_canonicalVectorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ‖canonicalVectorMoment A H ρ ξ‖ = ‖vectorMoment A H ρ ξ‖ := by
  calc
    ‖canonicalVectorMoment A H ρ ξ‖ =
        ‖(tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A))
          (vectorMoment A H ρ ξ)‖ := by
          exact (firstArensIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map _
    _ = ‖vectorMoment A H ρ ξ‖ :=
      (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map _

theorem norm_canonicalMatrixCoefficient
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    ‖canonicalMatrixCoefficient A H ρ η ξ‖ =
      ‖matrixCoefficient A H ρ η ξ‖ := by
  calc
    ‖canonicalMatrixCoefficient A H ρ η ξ‖ =
        ‖(tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A))
          (matrixCoefficient A H ρ η ξ)‖ := by
          exact (firstArensIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map _
    _ = ‖matrixCoefficient A H ρ η ξ‖ :=
      (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map _

theorem canonicalVectorMoment_extends
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Extends (tensorDualIsometry (vectorMoment A H ρ ξ))
      (canonicalVectorMoment A H ρ ξ) := by
  intro a b
  exact firstArens_canonical (tensorDualIsometry (vectorMoment A H ρ ξ)) a b

theorem canonicalVectorMoment_normal
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    SeparatelyWeakStarContinuous (canonicalVectorMoment A H ρ ξ) := by
  exact separatelyWeakStarContinuous_firstExtension
    (vectorMoment A H ρ ξ) (isArensRegular_vectorMoment A H ρ ξ)

theorem canonicalMatrixCoefficient_normal
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    SeparatelyWeakStarContinuous
      (canonicalMatrixCoefficient A H ρ η ξ) := by
  exact separatelyWeakStarContinuous_firstExtension
    (matrixCoefficient A H ρ η ξ)
    (isArensRegular_matrixCoefficient A H ρ η ξ)

theorem canonicalMatrixCoefficient_apply
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) (a b : A) :
    BidualForm.eval (canonicalMatrixCoefficient A H ρ η ξ)
      (NormedSpace.inclusionInDoubleDual ℂ A a)
      (NormedSpace.inclusionInDoubleDual ℂ A b) =
        (matrixCoefficient A H ρ η ξ) (tprod ℂ A A a b) := by
  exact (firstArens_canonical
    (tensorDualIsometry (matrixCoefficient A H ρ η ξ)) a b).trans
      (tensorDualIsometry_apply (matrixCoefficient A H ρ η ξ) a b)

/-- The new bilinear isometry chooses exactly the already proved concrete
vector-product Arens extension, rather than an unrelated existence witness. -/
theorem canonicalMatrixCoefficient_eq_vectorProductExtension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    canonicalMatrixCoefficient A H ρ η ξ =
      MathlibAnnex.CStarAlgebra.VectorForms.vectorProductExtension ρ η ξ := by
  rw [canonicalMatrixCoefficient,
    tensorDual_matrixCoefficient_eq_vectorProductForm]
  rfl

theorem canonicalVectorMoment_apply
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a b : A) :
    BidualForm.eval (canonicalVectorMoment A H ρ ξ)
      (NormedSpace.inclusionInDoubleDual ℂ A a)
      (NormedSpace.inclusionInDoubleDual ℂ A b) =
        (vectorMoment A H ρ ξ) (tprod ℂ A A a b) := by
  simpa only [tensorDualIsometry_apply] using
    canonicalVectorMoment_extends A H ρ ξ a b

theorem canonicalVectorTensorMoment_bilinear
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    tensorDualIsometry (canonicalVectorTensorMoment A H ρ ξ) =
      canonicalVectorMoment A H ρ ξ := by
  simp [canonicalVectorTensorMoment, canonicalVectorMoment,
    firstExtensionIsometry]

theorem norm_canonicalVectorTensorMoment
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ‖canonicalVectorTensorMoment A H ρ ξ‖ = ‖vectorMoment A H ρ ξ‖ := by
  exact (firstExtensionIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map _

end MathlibAnnex.CStarAlgebra.TensorAveraging
