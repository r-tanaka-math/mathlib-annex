/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel

/-!
# Equal-kernel descent through actual representation images

The standard hom-kernel quotient and original operator norms are retained.
No compact containment, irreducibility, or spectrum comparison is assumed.
-/


set_option autoImplicit false
noncomputable section
open Set InnerProductSpace
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
open NonUnitalCStarRepresentation

namespace NonUnitalCStarRepresentation

variable {A : Type w} [NonUnitalCStarAlgebra A]
private def equalKernelContinuousMap (q : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

variable (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A L)

/-- Actual two-sided kernel equality is also equality of the closed linear kernels. -/
theorem ker_eq_of_kernelIdeal_eq (hker : kernelIdeal pi = kernelIdeal rho) :
    (equalKernelContinuousMap pi).ker = (equalKernelContinuousMap rho).ker := by
  ext a
  change pi a = 0 ↔ rho a = 0
  rw [← mem_kernelIdeal pi a, ← mem_kernelIdeal rho a, hker]

/-- The standard hom-kernel quotients are star-linearly equivalent when their
actual kernels agree. No arbitrary-closed-ideal quotient is postulated. -/
def homKernelQuotientEquiv (hker : kernelIdeal pi = kernelIdeal rho) :
    HomKernelQuotient pi ≃⋆ₐ[ℂ] HomKernelQuotient rho := by
  let E := Submodule.quotEquivOfEq _ _ (ker_eq_of_kernelIdeal_eq pi rho hker)
  refine { E.toEquiv with
    map_add' := E.map_add
    map_smul' := E.map_smul
    map_mul' := ?_
    map_star' := ?_ }
  · intro x y
    obtain ⟨a, rfl⟩ := HomKernelQuotient.mk_surjective pi x
    obtain ⟨b, rfl⟩ := HomKernelQuotient.mk_surjective pi y
    rw [← HomKernelQuotient.mk_mul]
    change HomKernelQuotient.mk rho (a * b) =
      HomKernelQuotient.mk rho a * HomKernelQuotient.mk rho b
    exact HomKernelQuotient.mk_mul rho a b
  · intro x
    obtain ⟨a, rfl⟩ := HomKernelQuotient.mk_surjective pi x
    rw [← HomKernelQuotient.mk_star]
    change HomKernelQuotient.mk rho (star a) = star (HomKernelQuotient.mk rho a)
    exact HomKernelQuotient.mk_star rho a

@[simp]
theorem homKernelQuotientEquiv_mk (hker : kernelIdeal pi = kernelIdeal rho) (a : A) :
    homKernelQuotientEquiv pi rho hker (HomKernelQuotient.mk pi a) =
      HomKernelQuotient.mk rho a := rfl

/-- A concrete equivalence of the two literal ranges, through the existing
isometric quotient-to-image equivalences. -/
def imageEquivOfKernelEq (hker : kernelIdeal pi = kernelIdeal rho) :
    (NonUnitalStarAlgHom.range pi) ≃⋆ₐ[ℂ] (NonUnitalStarAlgHom.range rho) :=
  ((HomKernelQuotient.imageStarAlgEquiv pi).symm.trans
    (homKernelQuotientEquiv pi rho hker)).trans
      (HomKernelQuotient.imageStarAlgEquiv rho)

@[simp]
theorem imageEquivOfKernelEq_apply (hker : kernelIdeal pi = kernelIdeal rho) (a : A) :
    imageEquivOfKernelEq pi rho hker ((NonUnitalStarAlgHom.rangeRestrict pi) a) = (NonUnitalStarAlgHom.rangeRestrict rho) a := by
  unfold imageEquivOfKernelEq
  change HomKernelQuotient.imageStarAlgEquiv rho
    (homKernelQuotientEquiv pi rho hker
      ((HomKernelQuotient.imageStarAlgEquiv pi).symm ((NonUnitalStarAlgHom.rangeRestrict pi) a))) = _
  rw [← HomKernelQuotient.imageStarAlgEquiv_mk pi a,
    StarAlgEquiv.symm_apply_apply, homKernelQuotientEquiv_mk,
    HomKernelQuotient.imageStarAlgEquiv_mk]

/-- The representation of the actual image whose pullback is rho itself. -/
def factorThroughImage (hker : kernelIdeal pi = kernelIdeal rho) :
    (NonUnitalStarAlgHom.range pi) →⋆ₙₐ[ℂ] (L →L[ℂ] L) :=
  (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range rho)).comp
    (imageEquivOfKernelEq pi rho hker).toNonUnitalStarAlgHom

@[simp]
theorem factorThroughImage_apply (hker : kernelIdeal pi = kernelIdeal rho) (a : A) :
    factorThroughImage pi rho hker ((NonUnitalStarAlgHom.rangeRestrict pi) a) = rho a := by
  change (imageEquivOfKernelEq pi rho hker ((NonUnitalStarAlgHom.rangeRestrict pi) a)).val = rho a
  rw [imageEquivOfKernelEq_apply]
  rfl

/-- Equality of the whole homomorphisms, not merely equality on some generators. -/
theorem factorThroughImage_comp_rangeRestrict (hker : kernelIdeal pi = kernelIdeal rho) :
    (factorThroughImage pi rho hker).comp (NonUnitalStarAlgHom.rangeRestrict pi) = rho := by
  apply NonUnitalStarAlgHom.ext
  intro a
  exact factorThroughImage_apply pi rho hker a

theorem factorThroughImage_injective (hker : kernelIdeal pi = kernelIdeal rho) :
    Function.Injective (factorThroughImage pi rho hker) := by
  intro a b hab
  apply (imageEquivOfKernelEq pi rho hker).injective
  exact Subtype.ext hab

/-- The descent is independent of representatives and uniquely determined by
its pullback through the actual surjective range restriction. -/
theorem factorThroughImage_unique (hker : kernelIdeal pi = kernelIdeal rho)
    (sigma : (NonUnitalStarAlgHom.range pi) →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hsigma : sigma.comp (NonUnitalStarAlgHom.rangeRestrict pi) = rho) :
    sigma = factorThroughImage pi rho hker := by
  apply NonUnitalStarAlgHom.ext
  intro b
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1 b.property
  have hb : (NonUnitalStarAlgHom.rangeRestrict pi) a = b := Subtype.ext ha
  rw [← hb, factorThroughImage_apply]
  exact congrArg (fun f : A →⋆ₙₐ[ℂ] (L →L[ℂ] L) => f a) hsigma

variable [PartialOrder A] [StarOrderedRing A]
local instance : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- The inherited operator norms, not transported substitute norms. -/
theorem isometry_factorThroughImage (hker : kernelIdeal pi = kernelIdeal rho) :
    Isometry (factorThroughImage pi rho hker) :=
  NonUnitalStarAlgHom.isometry _ (factorThroughImage_injective pi rho hker)

/-- Norm equality for every element of the original-norm image. -/
theorem norm_factorThroughImage (hker : kernelIdeal pi = kernelIdeal rho) (a : (NonUnitalStarAlgHom.range pi)) :
    ‖factorThroughImage pi rho hker a‖ = ‖a‖ := by
  simpa only [map_zero, dist_zero_right] using
    (isometry_factorThroughImage pi rho hker).dist_eq a 0

theorem continuous_factorThroughImage (hker : kernelIdeal pi = kernelIdeal rho) :
    Continuous (factorThroughImage pi rho hker) :=
  (isometry_factorThroughImage pi rho hker).continuous

/-- Reducing subspaces coincide via the surjective range restriction. -/
theorem reduces_factorThroughImage_iff (hker : kernelIdeal pi = kernelIdeal rho)
    (M : Submodule ℂ L) :
    NonUnitalCStarRepresentation.Reduces (factorThroughImage pi rho hker) M ↔ rho.Reduces M := by
  have h := reduces_comp_iff_of_surjective (factorThroughImage pi rho hker)
    (NonUnitalStarAlgHom.rangeRestrict pi) (rangeRestrict_surjective pi) M
  rw [factorThroughImage_comp_rangeRestrict pi rho hker] at h
  exact h.symm

theorem isIrreducible_factorThroughImage_iff (hker : kernelIdeal pi = kernelIdeal rho) :
    NonUnitalCStarRepresentation.IsIrreducible (factorThroughImage pi rho hker) ↔ rho.IsIrreducible := by
  have h := isIrreducible_comp_iff_of_surjective (factorThroughImage pi rho hker)
    (NonUnitalStarAlgHom.rangeRestrict pi) (rangeRestrict_surjective pi)
  rw [factorThroughImage_comp_rangeRestrict pi rho hker] at h
  exact h.symm

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
