import MathlibAnnex.Analysis.Normed.Bilinear.Bidual
import MathlibAnnex.Analysis.Normed.TensorProduct.Projective

/-!
# Bidual extensions of projective-tensor functionals

This file connects bounded bilinear forms and their Arens extensions to the
already fixed completed projective tensor product.  No auxiliary tensor norm
is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MathlibAnnex.ProjectiveTensorProduct

universe uK uE uF uE' uF'

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']
variable {F' : Type uF'} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedSpace ℝ F'] [IsScalarTower ℝ 𝕜 F']

open MathlibAnnex.BidualBilinear MathlibAnnex.FiniteApproximation
  MathlibAnnex.WeakCompact

namespace BoundedBilinearMap

private def toContinuousLinearMapLinear
    (B : BoundedBilinearMap 𝕜 E F 𝕜) : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂ 𝕜
    (fun x y ↦ apply 𝕜 E F 𝕜 B x y)
    (by
      intro x₁ x₂ y
      have hsum : Function.update (pair E F 0 y) (.inl PUnit.unit)
          (ULift.up x₁ + ULift.up x₂) = pair E F (x₁ + x₂) y := by
        funext i
        rcases i with i | i <;> cases i <;>
          simp [Function.update, pair] <;> apply ULift.ext <;> rfl
      have h₁ : Function.update (pair E F 0 y) (.inl PUnit.unit)
          (ULift.up x₁) = pair E F x₁ y := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h₂ : Function.update (pair E F 0 y) (.inl PUnit.unit)
          (ULift.up x₂) = pair E F x₂ y := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h := B.map_update_add (pair E F 0 y) (.inl PUnit.unit)
        (ULift.up x₁) (ULift.up x₂)
      change B (pair E F (x₁ + x₂) y) =
        B (pair E F x₁ y) + B (pair E F x₂ y)
      calc
        B (pair E F (x₁ + x₂) y) =
            B (Function.update (pair E F 0 y) (.inl PUnit.unit)
              (ULift.up x₁ + ULift.up x₂)) := congrArg B hsum.symm
        _ = B (Function.update (pair E F 0 y) (.inl PUnit.unit)
              (ULift.up x₁)) +
            B (Function.update (pair E F 0 y) (.inl PUnit.unit)
              (ULift.up x₂)) := h
        _ = B (pair E F x₁ y) + B (pair E F x₂ y) :=
          congrArg₂ (· + ·) (congrArg B h₁) (congrArg B h₂))
    (by
      intro c x y
      have hsmul : Function.update (pair E F 0 y) (.inl PUnit.unit)
          (c • ULift.up x) = pair E F (c • x) y := by
        funext i
        rcases i with i | i <;> cases i <;>
          simp [Function.update, pair] <;> apply ULift.ext <;> rfl
      have hx : Function.update (pair E F 0 y) (.inl PUnit.unit)
          (ULift.up x) = pair E F x y := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h := B.map_update_smul (pair E F 0 y) (.inl PUnit.unit) c
        (ULift.up x)
      change B (pair E F (c • x) y) = c • B (pair E F x y)
      calc
        B (pair E F (c • x) y) =
            B (Function.update (pair E F 0 y) (.inl PUnit.unit)
              (c • ULift.up x)) := congrArg B hsmul.symm
        _ = c • B (Function.update (pair E F 0 y) (.inl PUnit.unit)
              (ULift.up x)) := h
        _ = c • B (pair E F x y) :=
          congrArg (fun z ↦ c • z) (congrArg B hx))
    (by
      intro x y₁ y₂
      have hsum : Function.update (pair E F x 0) (.inr PUnit.unit)
          (ULift.up y₁ + ULift.up y₂) = pair E F x (y₁ + y₂) := by
        funext i
        rcases i with i | i <;> cases i <;>
          simp [Function.update, pair] <;> apply ULift.ext <;> rfl
      have h₁ : Function.update (pair E F x 0) (.inr PUnit.unit)
          (ULift.up y₁) = pair E F x y₁ := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h₂ : Function.update (pair E F x 0) (.inr PUnit.unit)
          (ULift.up y₂) = pair E F x y₂ := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h := B.map_update_add (pair E F x 0) (.inr PUnit.unit)
        (ULift.up y₁) (ULift.up y₂)
      change B (pair E F x (y₁ + y₂)) =
        B (pair E F x y₁) + B (pair E F x y₂)
      calc
        B (pair E F x (y₁ + y₂)) =
            B (Function.update (pair E F x 0) (.inr PUnit.unit)
              (ULift.up y₁ + ULift.up y₂)) := congrArg B hsum.symm
        _ = B (Function.update (pair E F x 0) (.inr PUnit.unit)
              (ULift.up y₁)) +
            B (Function.update (pair E F x 0) (.inr PUnit.unit)
              (ULift.up y₂)) := h
        _ = B (pair E F x y₁) + B (pair E F x y₂) :=
          congrArg₂ (· + ·) (congrArg B h₁) (congrArg B h₂))
    (by
      intro c x y
      have hsmul : Function.update (pair E F x 0) (.inr PUnit.unit)
          (c • ULift.up y) = pair E F x (c • y) := by
        funext i
        rcases i with i | i <;> cases i <;>
          simp [Function.update, pair] <;> apply ULift.ext <;> rfl
      have hy : Function.update (pair E F x 0) (.inr PUnit.unit)
          (ULift.up y) = pair E F x y := by
        funext i
        rcases i with i | i <;> cases i <;> simp [Function.update, pair]
      have h := B.map_update_smul (pair E F x 0) (.inr PUnit.unit) c
        (ULift.up y)
      change B (pair E F x (c • y)) = c • B (pair E F x y)
      calc
        B (pair E F x (c • y)) =
            B (Function.update (pair E F x 0) (.inr PUnit.unit)
              (c • ULift.up y)) := congrArg B hsmul.symm
        _ = c • B (Function.update (pair E F x 0) (.inr PUnit.unit)
              (ULift.up y)) := h
        _ = c • B (pair E F x y) :=
          congrArg (fun z ↦ c • z) (congrArg B hy))

/-- Curry a bounded bilinear map without changing its operator norm. -/
def toContinuousLinearMap (B : BoundedBilinearMap 𝕜 E F 𝕜) :
    E →L[𝕜] F →L[𝕜] 𝕜 :=
  (toContinuousLinearMapLinear B).mkContinuous₂ ‖B‖ fun x y ↦ by
    change ‖apply 𝕜 E F 𝕜 B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖
    have h := B.le_opNorm (pair E F x y)
    change ‖apply 𝕜 E F 𝕜 B x y‖ ≤
      ‖B‖ * ∏ i, ‖pair E F x y i‖ at h
    simpa [Fintype.prod_sum_type, pair, mul_assoc] using h

@[simp]
theorem toContinuousLinearMap_apply
    (B : BoundedBilinearMap 𝕜 E F 𝕜) (x : E) (y : F) :
    toContinuousLinearMap B x y = apply 𝕜 E F 𝕜 B x y := rfl

@[simp]
theorem norm_toContinuousLinearMap
    (B : BoundedBilinearMap 𝕜 E F 𝕜) :
    ‖toContinuousLinearMap B‖ = ‖B‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _
  · refine ContinuousMultilinearMap.opNorm_le_bound
      (f := B) (norm_nonneg (toContinuousLinearMap B)) fun m ↦ ?_
    let x : E := (m (.inl PUnit.unit)).down
    let y : F := (m (.inr PUnit.unit)).down
    have hm : m = pair E F x y := by
      funext i
      rcases i with i | i <;> cases i <;> rfl
    rw [hm]
    have h := (toContinuousLinearMap B).le_opNorm₂ x y
    change ‖apply 𝕜 E F 𝕜 B x y‖ ≤
      ‖toContinuousLinearMap B‖ * ‖x‖ * ‖y‖ at h
    change ‖apply 𝕜 E F 𝕜 B x y‖ ≤
      ‖toContinuousLinearMap B‖ * ∏ i, ‖pair E F x y i‖
    simpa [Fintype.prod_sum_type, pair, mul_assoc] using h

@[simp]
theorem toContinuousLinearMap_ofContinuousLinearMap
    (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    toContinuousLinearMap (ofContinuousLinearMap 𝕜 E F 𝕜 B) = B := by
  ext x y
  rfl

@[simp]
theorem ofContinuousLinearMap_toContinuousLinearMap
    (B : BoundedBilinearMap 𝕜 E F 𝕜) :
    ofContinuousLinearMap 𝕜 E F 𝕜 (toContinuousLinearMap B) = B := by
  apply DFunLike.ext _ _
  intro m
  let x : E := (m (.inl PUnit.unit)).down
  let y : F := (m (.inr PUnit.unit)).down
  have hm : m = pair E F x y := by
    funext i
    rcases i with i | i <;> cases i <;> rfl
  rw [hm]
  rfl

/-- Isometric equivalence between the balanced multilinear and ordinary
curried presentations of bounded bilinear forms. -/
def curriedIsometry :
    BoundedBilinearMap 𝕜 E F 𝕜 ≃ₗᵢ[𝕜] (E →L[𝕜] F →L[𝕜] 𝕜) where
  toFun := toContinuousLinearMap
  invFun := ofContinuousLinearMap 𝕜 E F 𝕜
  left_inv := ofContinuousLinearMap_toContinuousLinearMap
  right_inv := toContinuousLinearMap_ofContinuousLinearMap
  map_add' B C := by ext x y; rfl
  map_smul' c B := by ext x y; rfl
  norm_map' := norm_toContinuousLinearMap

end BoundedBilinearMap

/-- The actual dual of the completed projective tensor product is
isometrically the ordinary curried space of bounded bilinear forms. -/
def tensorDualIsometry :
    StrongDual 𝕜 (Completion 𝕜 E F) ≃ₗᵢ[𝕜]
      (E →L[𝕜] F →L[𝕜] 𝕜) :=
  (dualIsometry 𝕜 E F).trans BoundedBilinearMap.curriedIsometry

@[simp]
theorem tensorDualIsometry_apply
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) (x : E) (y : F) :
    tensorDualIsometry f x y = f (tprod 𝕜 E F x y) := by
  change BoundedBilinearMap.apply 𝕜 E F 𝕜
    (dualIsometry 𝕜 E F f) x y = _
  exact dualIsometry_apply 𝕜 E F f x y

/-- Arens regularity of an actual projective-tensor dual functional. -/
def IsArensRegular (f : StrongDual 𝕜 (Completion 𝕜 E F)) : Prop :=
  IsWeaklyCompact (tensorDualIsometry f)

theorem isArensRegular_iff_extensions_eq
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    IsArensRegular f ↔
      firstArens (tensorDualIsometry f) =
        secondArens (tensorDualIsometry f) :=
  isWeaklyCompact_iff_firstArens_eq_secondArens _

theorem isArensRegular_iff_exists_extension
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    IsArensRegular f ↔
      ∃ C : BidualForm 𝕜 E F,
        SeparatelyWeakStarContinuous C ∧
        Extends (tensorDualIsometry f) C ∧ ‖C‖ = ‖f‖ := by
  rw [IsArensRegular, isWeaklyCompact_iff_exists_extension]
  simp only [(tensorDualIsometry (𝕜 := 𝕜) (E := E) (F := F)).norm_map]

/-- The first Arens extension as a functional on the same completed
projective tensor construction, applied to the isometric bidual models. -/
def firstExtensionFunctional
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    StrongDual 𝕜
      (Completion 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)) :=
  liftIsometry 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜 <|
    BoundedBilinearMap.ofContinuousLinearMap 𝕜
      (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜 <|
        firstArens (tensorDualIsometry f)

/-- The second Arens extension as a projective-tensor functional. -/
def secondExtensionFunctional
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    StrongDual 𝕜
      (Completion 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)) :=
  liftIsometry 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜 <|
    BoundedBilinearMap.ofContinuousLinearMap 𝕜
      (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜 <|
        secondArens (tensorDualIsometry f)

@[simp]
theorem firstExtensionFunctional_tprod
    (f : StrongDual 𝕜 (Completion 𝕜 E F))
    (x : StrongDual 𝕜 (StrongDual 𝕜 E))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    firstExtensionFunctional f
      (tprod 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)
        (ULift.up x) (ULift.up y)) =
      BidualForm.eval (firstArens (tensorDualIsometry f)) x y := by
  simp [firstExtensionFunctional, BidualForm.eval]

@[simp]
theorem secondExtensionFunctional_tprod
    (f : StrongDual 𝕜 (Completion 𝕜 E F))
    (x : StrongDual 𝕜 (StrongDual 𝕜 E))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    secondExtensionFunctional f
      (tprod 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)
        (ULift.up x) (ULift.up y)) =
      BidualForm.eval (secondArens (tensorDualIsometry f)) x y := by
  simp [secondExtensionFunctional, BidualForm.eval]

@[simp]
theorem norm_firstExtensionFunctional
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    ‖firstExtensionFunctional f‖ = ‖f‖ := by
  rw [firstExtensionFunctional,
    (liftIsometry 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜).norm_map,
    BoundedBilinearMap.norm_ofContinuousLinearMap,
    norm_firstArens,
    (tensorDualIsometry (𝕜 := 𝕜) (E := E) (F := F)).norm_map]

@[simp]
theorem norm_secondExtensionFunctional
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    ‖secondExtensionFunctional f‖ = ‖f‖ := by
  rw [secondExtensionFunctional,
    (liftIsometry 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F) 𝕜).norm_map,
    BoundedBilinearMap.norm_ofContinuousLinearMap,
    norm_secondArens,
    (tensorDualIsometry (𝕜 := 𝕜) (E := E) (F := F)).norm_map]

theorem isArensRegular_iff_tensor_extensions_eq
    (f : StrongDual 𝕜 (Completion 𝕜 E F)) :
    IsArensRegular f ↔
      firstExtensionFunctional f = secondExtensionFunctional f := by
  rw [isArensRegular_iff_extensions_eq]
  constructor
  · intro h
    simp [firstExtensionFunctional, secondExtensionFunctional, h]
  · intro h
    apply BidualForm.ext
    intro x y
    have hxy := congrArg (fun q : StrongDual 𝕜
        (Completion 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)) ↦
      q (tprod 𝕜 (BidualModel 𝕜 E) (BidualModel 𝕜 F)
        (ULift.up x) (ULift.up y))) h
    simpa using hxy

end

end MathlibAnnex.ProjectiveTensorProduct
