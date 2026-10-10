/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageDual

/-!
# Relative weak-star topology on the image-dual annihilator

The first stage is precomposition by the standard-quotient-to-image isometry.
The second stage is MAIN's `Submodule.quotientWeakDualHomeomorph`. Pointwise
continuity of the reverse map uses evaluation at a representative, never a
continuous choice of representatives or the norm topology on the dual.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable (q : A →⋆ₙₐ[ℂ] B)

private def weakImageContinuousMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  ({ toFun := q
     map_add' := map_add q
     map_smul' := map_smul q } : A →ₗ[ℂ] B).mkContinuous 1
    (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- The first stage of the weak-star comparison has the same underlying linear map. -/
def imageWeakDualToQuotientEquiv :
    WeakDual ℂ (NonUnitalStarAlgHom.range q) ≃ₗ[ℂ] WeakDual ℂ (A ⧸ (weakImageContinuousMap q).ker) :=
  WeakDual.toStrongDual.trans
    ((imageDualToQuotientLinearIsometryEquiv q).toLinearEquiv.trans StrongDual.toWeakDual)

@[simp]
theorem imageWeakDualToQuotientEquiv_apply (f : WeakDual ℂ (NonUnitalStarAlgHom.range q))
    (z : A ⧸ (weakImageContinuousMap q).ker) :
    imageWeakDualToQuotientEquiv q f z =
      f (standardQuotientImageLinearIsometryEquiv q z) := rfl

@[simp]
theorem imageWeakDualToQuotientEquiv_symm_apply
    (g : WeakDual ℂ (A ⧸ (weakImageContinuousMap q).ker)) (b : (NonUnitalStarAlgHom.range q)) :
    (imageWeakDualToQuotientEquiv q).symm g b =
      g ((standardQuotientImageLinearIsometryEquiv q).symm b) := rfl

theorem continuous_imageWeakDualToQuotientEquiv :
    Continuous (imageWeakDualToQuotientEquiv q) := by
  apply WeakDual.continuous_of_continuous_eval
  intro z
  exact WeakDual.eval_continuous (standardQuotientImageLinearIsometryEquiv q z)

theorem continuous_imageWeakDualToQuotientEquiv_symm :
    Continuous (imageWeakDualToQuotientEquiv q).symm := by
  apply WeakDual.continuous_of_continuous_eval
  intro b
  exact WeakDual.eval_continuous ((standardQuotientImageLinearIsometryEquiv q).symm b)

def imageWeakDualToQuotientHomeomorph :
    WeakDual ℂ (NonUnitalStarAlgHom.range q) ≃ₜ WeakDual ℂ (A ⧸ (weakImageContinuousMap q).ker) where
  toEquiv := (imageWeakDualToQuotientEquiv q).toEquiv
  continuous_toFun := continuous_imageWeakDualToQuotientEquiv q
  continuous_invFun := continuous_imageWeakDualToQuotientEquiv_symm q

/-- The actual image weak dual and the ORIGINAL kernel's relative weak dual annihilator. -/
def imageWeakDualHomeomorph :
    WeakDual ℂ (NonUnitalStarAlgHom.range q) ≃ₜ (weakImageContinuousMap q).ker.weakDualAnnihilator :=
  (imageWeakDualToQuotientHomeomorph q).trans
    (weakImageContinuousMap q).ker.quotientWeakDualHomeomorph

@[simp]
theorem imageWeakDualHomeomorph_apply_apply (f : WeakDual ℂ (NonUnitalStarAlgHom.range q)) (a : A) :
    (imageWeakDualHomeomorph q f).val a = f ((NonUnitalStarAlgHom.rangeRestrict q) a) := by
  change f (standardQuotientImageLinearIsometryEquiv q
    ((weakImageContinuousMap q).ker.mkQ a)) = f ((NonUnitalStarAlgHom.rangeRestrict q) a)
  exact congrArg (fun z => f z) (standardQuotientImageLinearIsometryEquiv_mk q a)

/-- Strong-dual and weak-dual bundles have exactly the same evaluation formula. -/
theorem toStrongDual_imageWeakDualHomeomorph (f : WeakDual ℂ (NonUnitalStarAlgHom.range q)) :
    WeakDual.toStrongDual (imageWeakDualHomeomorph q f).val =
      (imageDualLinearIsometryEquiv q (WeakDual.toStrongDual f)).val := by
  ext a
  change (imageWeakDualHomeomorph q f).val a =
    (imageDualLinearIsometryEquiv q (WeakDual.toStrongDual f)).val a
  rw [imageWeakDualHomeomorph_apply_apply, imageDualLinearIsometryEquiv_apply_apply]
  rfl

/-- Inverse evaluation at any representative, without assuming a section continuous. -/
@[simp]
theorem imageWeakDualHomeomorph_symm_apply_image
    (g : (weakImageContinuousMap q).ker.weakDualAnnihilator) (a : A) :
    (imageWeakDualHomeomorph q).symm g ((NonUnitalStarAlgHom.rangeRestrict q) a) = g.val a := by
  have h := congrArg (fun k : (weakImageContinuousMap q).ker.weakDualAnnihilator => k.val a)
    ((imageWeakDualHomeomorph q).apply_symm_apply g)
  simpa only [imageWeakDualHomeomorph_apply_apply] using h

end MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient
