import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Arens
import MathlibAnnex.Analysis.Normed.TensorProduct.BidualForms

/-!
# Canonical Arens extension on projective-tensor duals

The first and second Arens extensions are transported through the existing
isometric identification of the dual of the completed projective tensor
product.  In particular, the transport is linear and norm preserving; no
second tensor norm or second completion is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MathlibAnnex.ProjectiveTensorProduct

open MathlibAnnex.BidualBilinear

universe uK uE uF

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The first Arens extension, transported to the dual of the completed
projective tensor product on the two bidual models. -/
def firstExtensionIsometry :
    StrongDual 𝕜 (Completion 𝕜 E F) →ₗᵢ[𝕜]
      StrongDual 𝕜
        (Completion 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)) :=
  (tensorDualIsometry
      (𝕜 := 𝕜) (E := BidualModel 𝕜 E) (F := BidualModel 𝕜 F)).symm.toLinearIsometry.comp
    (firstArensIsometry.comp
      (tensorDualIsometry (𝕜 := 𝕜) (E := E) (F := F)).toLinearIsometry)

/-- The second Arens extension, with the same linear isometric transport. -/
def secondExtensionIsometry :
    StrongDual 𝕜 (Completion 𝕜 E F) →ₗᵢ[𝕜]
      StrongDual 𝕜
        (Completion 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)) :=
  (tensorDualIsometry
      (𝕜 := 𝕜) (E := BidualModel 𝕜 E) (F := BidualModel 𝕜 F)).symm.toLinearIsometry.comp
    (secondArensIsometry.comp
      (tensorDualIsometry (𝕜 := 𝕜) (E := E) (F := F)).toLinearIsometry)

/-- The canonical tensor-dual extension is separately weak-star continuous
whenever the associated bilinear operator is weakly compact. -/
theorem separatelyWeakStarContinuous_firstExtension
    (f : StrongDual 𝕜 (Completion 𝕜 E F))
    (hf : IsArensRegular f) :
    SeparatelyWeakStarContinuous
      (firstArens (tensorDualIsometry f)) :=
  separatelyWeakStarContinuous_firstArens _ hf

/-- Pointwise naturality of the canonical tensor-dual extension under
bounded maps on both factors. -/
theorem firstExtension_natural_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
      [NormedSpace ℝ F'] [IsScalarTower ℝ 𝕜 F']
    (f : StrongDual 𝕜 (Completion 𝕜 E F))
    (U : E' →L[𝕜] E) (V : F' →L[𝕜] F)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E'))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F')) :
    BidualForm.eval
        (firstArens (precompRight ((tensorDualIsometry f).comp U) V)) x y =
      BidualForm.eval (firstArens (tensorDualIsometry f))
        (MathlibAnnex.WeakCompact.bidualMap U x)
        (MathlibAnnex.WeakCompact.bidualMap V y) :=
  firstArens_precomp_apply _ U V x y

end

end MathlibAnnex.ProjectiveTensorProduct
