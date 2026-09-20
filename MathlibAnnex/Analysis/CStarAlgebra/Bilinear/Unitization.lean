import Mathlib.Analysis.CStarAlgebra.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Arens

/-!
# Reduction of weak compactness to the unitization

An arbitrary bounded bilinear form on a nonunital C-star algebra extends
canonically along the bounded projection from the minimal unitization.  This
file proves that weak compactness of that concrete extension implies weak
compactness of the original form.  Thus a universal theorem for unital
C-star algebras immediately covers the genuinely nonunital case; no
faithfulness or approximate identity is assumed.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.BidualBilinear
open MathlibAnnex.WeakCompact

universe uA

noncomputable section

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- The canonical isometric inclusion into the minimal unitization, bundled
as a continuous linear map. -/
def unitizationInclusion : A →L[ℂ] Unitization ℂ A where
  toLinearMap := Unitization.inrHom ℂ ℂ A
  cont := Unitization.continuous_inr

@[simp]
theorem unitizationInclusion_apply (x : A) :
    unitizationInclusion x = (x : Unitization ℂ A) :=
  rfl

/-- The bounded linear projection from the minimal unitization onto its
nonunital summand. -/
def unitizationProjection : Unitization ℂ A →L[ℂ] A where
  toLinearMap := Unitization.sndHom ℂ ℂ A
  cont := Unitization.continuous_snd

@[simp]
theorem unitizationProjection_apply (x : Unitization ℂ A) :
    unitizationProjection x = x.snd :=
  rfl

@[simp]
theorem unitizationProjection_inclusion (x : A) :
    unitizationProjection (unitizationInclusion x) = x := by
  simp [unitizationProjection, unitizationInclusion]

/-- Extend a bilinear form from a nonunital algebra to its minimal
unitization by projecting both arguments to the original algebra. -/
def unitizationExtension (B : A →L[ℂ] A →L[ℂ] ℂ) :
    Unitization ℂ A →L[ℂ] Unitization ℂ A →L[ℂ] ℂ :=
  precompRight (B.comp unitizationProjection) unitizationProjection

@[simp]
theorem unitizationExtension_apply
    (B : A →L[ℂ] A →L[ℂ] ℂ) (x y : Unitization ℂ A) :
    unitizationExtension B x y = B x.snd y.snd :=
  rfl

@[simp]
theorem unitizationExtension_inclusion
    (B : A →L[ℂ] A →L[ℂ] ℂ) (x y : A) :
    unitizationExtension B (unitizationInclusion x)
      (unitizationInclusion y) = B x y := by
  simp [unitizationExtension]

/-- Restriction of functionals along the canonical inclusion. -/
def restrictUnitizationDual :
    StrongDual ℂ (Unitization ℂ A) →L[ℂ] StrongDual ℂ A :=
  (ContinuousLinearMap.compL ℂ A (Unitization ℂ A) ℂ).flip
    unitizationInclusion

@[simp]
theorem restrictUnitizationDual_apply
    (f : StrongDual ℂ (Unitization ℂ A)) (x : A) :
    restrictUnitizationDual f x = f (unitizationInclusion x) :=
  rfl

/-- Weak compactness descends from the canonical unitization extension.
This is the exact reduction needed after proving the unital universal
bilinear-form theorem. -/
theorem isWeaklyCompact_of_unitizationExtension
    (B : A →L[ℂ] A →L[ℂ] ℂ)
    (hB : IsWeaklyCompact (unitizationExtension B)) :
    IsWeaklyCompact B := by
  have hpre : IsWeaklyCompact
      ((unitizationExtension B).comp unitizationInclusion) :=
    isWeaklyCompact_precomp (unitizationExtension B) hB
      unitizationInclusion
  have hpost : IsWeaklyCompact
      (restrictUnitizationDual.comp
        ((unitizationExtension B).comp unitizationInclusion)) :=
    isWeaklyCompact_postcomp
      ((unitizationExtension B).comp unitizationInclusion) hpre
      restrictUnitizationDual
  have heq : restrictUnitizationDual.comp
      ((unitizationExtension B).comp unitizationInclusion) = B := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp [restrictUnitizationDual]
  rwa [heq] at hpost

end

end MathlibAnnex.CStarBilinear
