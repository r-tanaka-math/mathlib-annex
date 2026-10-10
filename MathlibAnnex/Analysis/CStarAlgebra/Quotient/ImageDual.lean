/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.Normed.Module.QuotientDual

/-!
# The dual of the actual image of a C-star homomorphism

The kernel quotient retains the standard quotient seminorm. Precomposition
with the already constructed quotient-to-image isometry is followed by the
shared quotient-dual equivalence. No second quotient-dual construction is
introduced, and the codomain is the full continuous annihilator.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (q : A →⋆ₙₐ[ℂ] B)

private def imageContinuousMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  ({ toFun := q
     map_add' := map_add q
     map_smul' := map_smul q } : A →ₗ[ℂ] B).mkContinuous 1
    (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

private def imageRangeContinuousMap (q : A →⋆ₙₐ[ℂ] B) :
    A →L[ℂ] (NonUnitalStarAlgHom.range q) :=
  LinearMap.mkContinuous
    { toFun := NonUnitalStarAlgHom.rangeRestrict q
      map_add' := map_add (NonUnitalStarAlgHom.rangeRestrict q)
      map_smul' := map_smul (NonUnitalStarAlgHom.rangeRestrict q) }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- The underlying linear quotient and norm are the original ones, by reduction. -/
def standardQuotientLinearIsometryEquiv :
    HomKernelQuotient q ≃ₗᵢ[ℂ] A ⧸ (imageContinuousMap q).ker where
  toLinearEquiv := LinearEquiv.refl ℂ _
  norm_map' _ := rfl

@[simp]
theorem standardQuotientLinearIsometryEquiv_mk (a : A) :
    standardQuotientLinearIsometryEquiv q (mk q a) =
      (imageContinuousMap q).ker.mkQ a := rfl

/-- In particular no image norm has replaced the standard quotient norm. -/
theorem norm_standardQuotientLinearIsometryEquiv (z : HomKernelQuotient q) :
    ‖standardQuotientLinearIsometryEquiv q z‖ = ‖z‖ := rfl

variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

-- Use the inherited range norm/module instances directly for the dual.

/-- The existing first-isomorphism isometry, expressed on the standard quotient type. -/
def standardQuotientImageLinearIsometryEquiv :
    (A ⧸ (imageContinuousMap q).ker) ≃ₗᵢ[ℂ] (NonUnitalStarAlgHom.range q) :=
  (standardQuotientLinearIsometryEquiv q).symm.trans (imageLinearIsometryEquiv q)

@[simp]
theorem standardQuotientImageLinearIsometryEquiv_mk (a : A) :
    standardQuotientImageLinearIsometryEquiv q ((imageContinuousMap q).ker.mkQ a) =
      (NonUnitalStarAlgHom.rangeRestrict q) a := by
  change imageStarAlgEquiv q (mk q a) = (NonUnitalStarAlgHom.rangeRestrict q) a
  exact imageStarAlgEquiv_mk q a

/-- Precomposition with the concrete first-isomorphism equivalence. -/
def imageDualToQuotientLinearIsometryEquiv :
    StrongDual ℂ (NonUnitalStarAlgHom.range q) ≃ₗᵢ[ℂ] StrongDual ℂ (A ⧸ (imageContinuousMap q).ker) := by
  let e := standardQuotientImageLinearIsometryEquiv q
  let L : StrongDual ℂ (NonUnitalStarAlgHom.range q) ≃ₗ[ℂ]
      StrongDual ℂ (A ⧸ (imageContinuousMap q).ker) :=
    { toFun f := f.comp e.toContinuousLinearEquiv.toContinuousLinearMap
      invFun f := f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      left_inv f := by
        ext x
        change f (e (e.symm x)) = f x
        rw [e.apply_symm_apply]
      right_inv f := by
        ext x
        change f (e.symm (e x)) = f x
        rw [e.symm_apply_apply]
      map_add' f g := by ext x; rfl
      map_smul' c f := by ext x; rfl }
  refine { toLinearEquiv := L, norm_map' := ?_ }
  intro f
  apply le_antisymm
  · apply (L f).opNorm_le_bound (norm_nonneg f)
    intro x
    change ‖f (e x)‖ ≤ ‖f‖ * ‖x‖
    simpa only [e.norm_map] using f.le_opNorm (e x)
  · apply f.opNorm_le_bound (norm_nonneg (L f))
    intro y
    have h := (L f).le_opNorm (e.symm y)
    change ‖f (e (e.symm y))‖ ≤ ‖L f‖ * ‖e.symm y‖ at h
    simpa only [e.apply_symm_apply, e.symm.norm_map] using h

@[simp]
theorem imageDualToQuotientLinearIsometryEquiv_apply (f : StrongDual ℂ (NonUnitalStarAlgHom.range q))
    (z : A ⧸ (imageContinuousMap q).ker) :
    imageDualToQuotientLinearIsometryEquiv q f z =
      f (standardQuotientImageLinearIsometryEquiv q z) := rfl

/-- The image dual is linearly isometric ONTO the full original-kernel annihilator. -/
def imageDualLinearIsometryEquiv :
    StrongDual ℂ (NonUnitalStarAlgHom.range q) ≃ₗᵢ[ℂ] (imageContinuousMap q).ker.strongDualAnnihilator :=
  (imageDualToQuotientLinearIsometryEquiv q).trans
    (imageContinuousMap q).ker.quotientDualLinearIsometryEquiv

@[simp]
theorem imageDualLinearIsometryEquiv_apply_apply (f : StrongDual ℂ (NonUnitalStarAlgHom.range q)) (a : A) :
    (imageDualLinearIsometryEquiv q f).val a = f ((NonUnitalStarAlgHom.rangeRestrict q) a) := by
  change f (standardQuotientImageLinearIsometryEquiv q
    ((imageContinuousMap q).ker.mkQ a)) = f ((NonUnitalStarAlgHom.rangeRestrict q) a)
  rw [standardQuotientImageLinearIsometryEquiv_mk]

/-- The inverse can be evaluated on ANY original representative. -/
@[simp]
theorem imageDualLinearIsometryEquiv_symm_apply_image
    (g : (imageContinuousMap q).ker.strongDualAnnihilator) (a : A) :
    (imageDualLinearIsometryEquiv q).symm g ((NonUnitalStarAlgHom.rangeRestrict q) a) = g.val a := by
  have h := congrArg (fun k : (imageContinuousMap q).ker.strongDualAnnihilator => k.val a)
    ((imageDualLinearIsometryEquiv q).apply_symm_apply g)
  simpa only [imageDualLinearIsometryEquiv_apply_apply] using h

/-- Set-level surjectivity is proved from the bundled equivalence, not presumed. -/
theorem range_comp_rangeRestrict_eq_strongDualAnnihilator :
    Set.range (fun f : StrongDual ℂ (NonUnitalStarAlgHom.range q) =>
      f.comp (imageRangeContinuousMap q)) =
        ((imageContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩ a ha
    have hqa : q a = 0 := ha
    change f ((NonUnitalStarAlgHom.rangeRestrict q) a) = 0
    rw [show (NonUnitalStarAlgHom.rangeRestrict q) a = 0 from Subtype.ext hqa, map_zero]
  · intro hg
    refine ⟨(imageDualLinearIsometryEquiv q).symm ⟨g, hg⟩, ?_⟩
    ext a
    exact imageDualLinearIsometryEquiv_symm_apply_image q ⟨g, hg⟩ a

end MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient
