/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.NormLift
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The genuine Banach quotient by a C-star homomorphism kernel

The norm and topology below are inherited from the standard quotient by the
closed linear kernel. They are not pulled back from the image. Only after
this quotient is complete do we prove that its induced map to the codomain
is isometric, using norm-minimizing fiber representatives from `NormLift`.
Closedness of the image is then a consequence, not an input.
This module does not construct a second generic quotient-dual API.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Explicit continuous-linear bundling of the same contractive homomorphism. -/
private def kernelContinuousMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  ({ toFun := q
     map_add' := map_add q
     map_smul' := map_smul q } : A →ₗ[ℂ] B).mkContinuous 1
    (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- The ordinary linear quotient by the actual homomorphism kernel. The type
wrapper permits C-star operations without installing them on unrelated
Banach quotients. -/
def HomKernelQuotient (q : A →⋆ₙₐ[ℂ] B) := A ⧸ (kernelContinuousMap q).ker

namespace HomKernelQuotient

variable (q : A →⋆ₙₐ[ℂ] B)

instance instNormedAddCommGroup : NormedAddCommGroup (HomKernelQuotient q) := by
  letI : IsClosed ((kernelContinuousMap q).ker : Set A) :=
    isClosed_eq (map_continuous q) continuous_const
  exact inferInstanceAs (NormedAddCommGroup (A ⧸ (kernelContinuousMap q).ker))

instance instNormedSpace : NormedSpace ℂ (HomKernelQuotient q) :=
  inferInstanceAs (NormedSpace ℂ (A ⧸ (kernelContinuousMap q).ker))

instance instCompleteSpace : CompleteSpace (HomKernelQuotient q) :=
  inferInstanceAs (CompleteSpace (A ⧸ (kernelContinuousMap q).ker))

/-- The standard continuous linear quotient map, with its original quotient norm. -/
def mk : A →L[ℂ] HomKernelQuotient q := (kernelContinuousMap q).ker.mkQL

/-- The induced continuous linear map to the original codomain. -/
def toCodomain : HomKernelQuotient q →L[ℂ] B :=
  (kernelContinuousMap q).ker.liftQL (kernelContinuousMap q) le_rfl

@[simp]
theorem toCodomain_mk (a : A) : toCodomain q (mk q a) = q a := rfl

theorem mk_surjective : Function.Surjective (mk q) := by
  intro x
  exact Quotient.inductionOn x (fun a => ⟨a, rfl⟩)

/-- Quotient equality is equality of images, not equality of representatives. -/
theorem mk_eq_mk_iff (a b : A) : mk q a = mk q b ↔ q a = q b := by
  change (Submodule.Quotient.mk a : A ⧸ (kernelContinuousMap q).ker) =
    Submodule.Quotient.mk b ↔ q a = q b
  rw [Submodule.Quotient.eq]
  change q (a - b) = 0 ↔ q a = q b
  rw [map_sub, sub_eq_zero]

theorem toCodomain_injective : Function.Injective (toCodomain q) := by
  intro x y h
  obtain ⟨a, rfl⟩ := mk_surjective q x
  obtain ⟨b, rfl⟩ := mk_surjective q y
  exact (mk_eq_mk_iff q a b).2 h

theorem norm_mk_le (a : A) : ‖mk q a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le (kernelContinuousMap q).ker a

/-- The lower norm estimate uses epsilon representatives of the actual
Banach quotient, and requires no image closedness. -/
theorem norm_toCodomain_le (x : HomKernelQuotient q) : ‖toCodomain q x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨a, ha, han⟩ := Submodule.Quotient.norm_mk_lt
    (S := (kernelContinuousMap q).ker) x hepsilon
  change mk q a = x at ha
  calc
    ‖toCodomain q x‖ = ‖q a‖ := by rw [← ha, toCodomain_mk]
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le q a
    _ ≤ ‖x‖ + epsilon := han.le

theorem range_toCodomain : Set.range (toCodomain q) = Set.range q := by
  ext b
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := mk_surjective q x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨mk q a, rfl⟩

variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

/-- Isometry is proved AFTER fixing the standard quotient norm. -/
theorem norm_toCodomain (x : HomKernelQuotient q) : ‖toCodomain q x‖ = ‖x‖ := by
  apply le_antisymm (norm_toCodomain_le q x)
  obtain ⟨a, rfl⟩ := mk_surjective q x
  obtain ⟨b, hb, hbn⟩ := exists_same_image_norm_eq q a
  have hclass : mk q b = mk q a := (mk_eq_mk_iff q b a).2 hb
  calc
    ‖mk q a‖ = ‖mk q b‖ := congrArg norm hclass.symm
    _ ≤ ‖b‖ := norm_mk_le q b
    _ = ‖toCodomain q (mk q a)‖ := hbn

theorem isometry_toCodomain : Isometry (toCodomain q) :=
  AddMonoidHomClass.isometry_of_norm (toCodomain q) (norm_toCodomain q)

/-- The original homomorphism image is norm-closed because it is the
isometric image of the complete standard quotient. -/
theorem isClosed_range : IsClosed (Set.range q) := by
  rw [← range_toCodomain q]
  exact (isometry_toCodomain q).isClosedEmbedding.isClosed_range

end HomKernelQuotient
end MathlibAnnex.Analysis.CStarAlgebra
