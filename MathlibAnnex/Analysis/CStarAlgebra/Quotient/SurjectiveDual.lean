/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageDual
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SurjectiveNorm

/-!
# The annihilator equivalence for a surjective C-star homomorphism

This adapter uses the actual image/standard-quotient construction and the
shared quotient dual. It does not construct a parallel generic Banach quotient
dual. Zero targets are allowed in the norm results in this file.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)

private def surjectiveDualMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- The actual image equals the codomain for a surjective map, preserving the norm. -/
def imageCodomainLinearIsometryEquiv : (NonUnitalStarAlgHom.range q) ≃ₗᵢ[ℂ] B where
  toLinearEquiv :=
    { toFun x := x.val
      invFun y := ⟨y, hq y⟩
      left_inv x := Subtype.ext rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  norm_map' _ := rfl

/-- Descend an actual annihilator element, through the already constructed image dual. -/
def descendAnnihilator (g : (surjectiveDualMap q).ker.strongDualAnnihilator) : StrongDual ℂ B :=
  ((HomKernelQuotient.imageDualLinearIsometryEquiv q).symm g).comp
    (imageCodomainLinearIsometryEquiv q hq).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem descendAnnihilator_apply (g : (surjectiveDualMap q).ker.strongDualAnnihilator)
    (a : A) : descendAnnihilator q hq g (q a) = g.val a := by
  change (HomKernelQuotient.imageDualLinearIsometryEquiv q).symm g
    ((imageCodomainLinearIsometryEquiv q hq).symm (q a)) = g.val a
  rw [show (imageCodomainLinearIsometryEquiv q hq).symm (q a) =
      (NonUnitalStarAlgHom.rangeRestrict q) a
    from Subtype.ext rfl]
  exact HomKernelQuotient.imageDualLinearIsometryEquiv_symm_apply_image q g a

/-- Actual pullback, as a linear isometry onto the full annihilator. -/
def surjectiveDualLinearIsometryEquiv :
    StrongDual ℂ B ≃ₗᵢ[ℂ] (surjectiveDualMap q).ker.strongDualAnnihilator where
  toLinearEquiv :=
    { toFun f := ⟨f.comp (surjectiveDualMap q), by
        intro a ha
        change f (q a) = 0
        rw [show q a = 0 from ha, map_zero]⟩
      invFun := descendAnnihilator q hq
      left_inv f := by
        ext b
        obtain ⟨a, rfl⟩ := hq b
        rw [descendAnnihilator_apply]
        rfl
      right_inv g := by
        apply Subtype.ext
        ext a
        exact descendAnnihilator_apply q hq g a
      map_add' f g := by apply Subtype.ext; ext a; rfl
      map_smul' c f := by apply Subtype.ext; ext a; rfl }
  norm_map' f := norm_comp_of_surjective_starHom q hq f

@[simp]
theorem surjectiveDualLinearIsometryEquiv_apply_apply (f : StrongDual ℂ B) (a : A) :
    (surjectiveDualLinearIsometryEquiv q hq f).val a = f (q a) := rfl

@[simp]
theorem surjectiveDualLinearIsometryEquiv_symm_apply_image
    (g : (surjectiveDualMap q).ker.strongDualAnnihilator) (a : A) :
    (surjectiveDualLinearIsometryEquiv q hq).symm g (q a) = g.val a :=
  descendAnnihilator_apply q hq g a

include hq in
/-- Equality with the annihilator is now established for ALL continuous functionals. -/
theorem range_comp_eq_strongDualAnnihilator_of_surjective :
    Set.range (fun f : StrongDual ℂ B => f.comp (surjectiveDualMap q)) =
      ((surjectiveDualMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩ a ha
    change f (q a) = 0
    rw [show q a = 0 from ha, map_zero]
  · intro hg
    refine ⟨(surjectiveDualLinearIsometryEquiv q hq).symm ⟨g, hg⟩, ?_⟩
    ext a
    exact surjectiveDualLinearIsometryEquiv_symm_apply_image q hq ⟨g, hg⟩ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.whnf.reducibleClassField false in
/-- A surjective normed-dual isometry carries its entire closed ball onto that of the subtype. -/
theorem image_closedBall_surjectiveDualLinearIsometryEquiv (r : ℝ) :
    surjectiveDualLinearIsometryEquiv q hq '' (Metric.closedBall 0 r) =
      Metric.closedBall 0 r := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    apply (mem_closedBall_zero_iff (a := surjectiveDualLinearIsometryEquiv q hq f) (r := r)).mpr
    rw [(surjectiveDualLinearIsometryEquiv q hq).norm_map]
    exact (mem_closedBall_zero_iff (a := f) (r := r)).mp hf
  · intro hg
    refine ⟨(surjectiveDualLinearIsometryEquiv q hq).symm g, ?_,
      (surjectiveDualLinearIsometryEquiv q hq).apply_symm_apply g⟩
    apply (mem_closedBall_zero_iff (a := (surjectiveDualLinearIsometryEquiv q hq).symm g) (r := r)).mpr
    rw [(surjectiveDualLinearIsometryEquiv q hq).symm.norm_map]
    exact (mem_closedBall_zero_iff (a := g) (r := r)).mp hg

end MathlibAnnex.Analysis.CStarAlgebra
