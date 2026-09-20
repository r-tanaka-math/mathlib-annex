import MathlibAnnex.Analysis.Normed.Bilinear.Bidual

/-!
# Functoriality of Arens extensions

This file packages the two canonical Arens extensions as linear isometries
and proves their naturality under bounded linear precomposition.  The
construction is valid for real and complex normed spaces; the C-star
application imports it in the forward direction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MathlibAnnex.WeakCompact

namespace MathlibAnnex.BidualBilinear

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

/-- The first Arens extension depends linearly and isometrically on the
original bounded bilinear form. -/
def firstArensIsometry :
    (E →L[𝕜] F →L[𝕜] 𝕜) →ₗᵢ[𝕜] BidualForm 𝕜 E F where
  toFun := firstArens
  map_add' B C := by
    apply BidualForm.ext
    intro x y
    change x (MathlibAnnex.FiniteApproximation.dualMap (B + C) y) =
      x (MathlibAnnex.FiniteApproximation.dualMap B y) +
        x (MathlibAnnex.FiniteApproximation.dualMap C y)
    simp [MathlibAnnex.FiniteApproximation.dualMap]
  map_smul' c B := by
    apply BidualForm.ext
    intro x y
    change x (MathlibAnnex.FiniteApproximation.dualMap (c • B) y) =
      c • x (MathlibAnnex.FiniteApproximation.dualMap B y)
    simp [MathlibAnnex.FiniteApproximation.dualMap]
  norm_map' := norm_firstArens

/-- The second Arens extension also depends linearly and isometrically on
the original bounded bilinear form. -/
def secondArensIsometry :
    (E →L[𝕜] F →L[𝕜] 𝕜) →ₗᵢ[𝕜] BidualForm 𝕜 E F where
  toFun := secondArens
  map_add' B C := by
    apply BidualForm.ext
    intro x y
    change y (MathlibAnnex.FiniteApproximation.dualMap (transpose (B + C)) x) =
      y (MathlibAnnex.FiniteApproximation.dualMap (transpose B) x) +
        y (MathlibAnnex.FiniteApproximation.dualMap (transpose C) x)
    simp [transpose, MathlibAnnex.FiniteApproximation.dualMap]
  map_smul' c B := by
    apply BidualForm.ext
    intro x y
    change y (MathlibAnnex.FiniteApproximation.dualMap (transpose (c • B)) x) =
      c • y (MathlibAnnex.FiniteApproximation.dualMap (transpose B) x)
    simp [transpose, MathlibAnnex.FiniteApproximation.dualMap]
  norm_map' := norm_secondArens

/-- Precompose the second variable of a curried bounded bilinear form. -/
def precompRight (B : E →L[𝕜] F →L[𝕜] 𝕜) (V : F' →L[𝕜] F) :
    E →L[𝕜] F' →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.precompR F' B).flip V

@[simp]
theorem precompRight_apply (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (V : F' →L[𝕜] F) (x : E) (y : F') :
    precompRight B V x y = B x (V y) := rfl

/-- Naturality of the first Arens extension under simultaneous bounded
linear precomposition in both variables. -/
theorem firstArens_precomp_apply
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (U : E' →L[𝕜] E) (V : F' →L[𝕜] F)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E'))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F')) :
    BidualForm.eval (firstArens (precompRight (B.comp U) V)) x y =
      BidualForm.eval (firstArens B) (bidualMap U x) (bidualMap V y) := rfl

/-- Naturality of the second Arens extension under simultaneous bounded
linear precomposition in both variables. -/
theorem secondArens_precomp_apply
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (U : E' →L[𝕜] E) (V : F' →L[𝕜] F)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E'))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F')) :
    BidualForm.eval (secondArens (precompRight (B.comp U) V)) x y =
      BidualForm.eval (secondArens B) (bidualMap U x) (bidualMap V y) := rfl

/-- Weak compactness makes the canonical first Arens extension separately
weak-star continuous.  No extension is selected by choice. -/
theorem separatelyWeakStarContinuous_firstArens
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (hB : IsWeaklyCompact B) :
    SeparatelyWeakStarContinuous (firstArens B) := by
  refine ⟨continuousFirst_firstArens B, ?_⟩
  have hEq := (isWeaklyCompact_iff_firstArens_eq_secondArens B).mp hB
  rw [hEq]
  exact continuousSecond_secondArens B

/-- If the domain is reflexive, every bounded operator from it is weakly
compact.  This small bridge is useful for genuine infinite-dimensional
Hilbert examples and does not assert reflexivity of a C-star algebra. -/
theorem isWeaklyCompact_of_reflexive_domain
    (B : E →L[𝕜] F) (hE : IsReflexive (𝕜 := 𝕜) E) :
    IsWeaklyCompact B := by
  have h := isWeaklyCompact_of_factorization
    (ContinuousLinearMap.id 𝕜 E) B hE
  simpa using h

end

end MathlibAnnex.BidualBilinear
