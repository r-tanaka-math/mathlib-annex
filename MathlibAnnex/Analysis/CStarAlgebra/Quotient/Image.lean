/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.KernelAlgebra
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The isometric first-isomorphism theorem onto the actual representation image

The range is `NonUnitalStarAlgHom.range q`, with its inherited subspace norm,
not an abstract algebra declared to be an image. Its closedness comes from
the complete standard kernel quotient. The equivalence below preserves
products, addition, complex scalars and star, and is isometric.
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

/-- Codomain restriction to the literal algebraic range. -/
def toImageHom : HomKernelQuotient q →⋆ₙₐ[ℂ] (NonUnitalStarAlgHom.range q) :=
  NonUnitalStarAlgHom.codRestrict (toCodomainHom q) (NonUnitalStarAlgHom.range q) fun x => by
    change toCodomain q x ∈ Set.range q
    rw [← range_toCodomain q]
    exact ⟨x, rfl⟩

@[simp]
theorem coe_toImageHom (x : HomKernelQuotient q) :
    (toImageHom q x : B) = toCodomain q x := rfl

theorem toImageHom_bijective : Function.Bijective (toImageHom q) := by
  constructor
  · intro x y h
    apply toCodomain_injective q
    exact congrArg Subtype.val h
  · intro b
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range q).mp b.property
    exact ⟨mk q a, Subtype.ext ha⟩

/-- The first-isomorphism equivalence, with the ACTUAL quotient and ACTUAL range. -/
def imageStarAlgEquiv : HomKernelQuotient q ≃⋆ₐ[ℂ] (NonUnitalStarAlgHom.range q) :=
  { Equiv.ofBijective (toImageHom q) (toImageHom_bijective q) with
    map_add' := map_add (toImageHom q)
    map_mul' := map_mul (toImageHom q)
    map_smul' := map_smul (toImageHom q)
    map_star' := map_star (toImageHom q) }

@[simp]
theorem imageStarAlgEquiv_apply (x : HomKernelQuotient q) :
    (imageStarAlgEquiv q x : B) = toCodomain q x := rfl

/-- The quotient-to-image map has the expected representative formula. -/
@[simp]
theorem imageStarAlgEquiv_mk (a : A) :
    imageStarAlgEquiv q (mk q a) = (NonUnitalStarAlgHom.rangeRestrict q) a := by
  apply Subtype.ext
  rfl

variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

/-- The algebraic range, with its original subspace norm, is norm-closed. -/
theorem isClosed_image : IsClosed ((NonUnitalStarAlgHom.range q) : Set B) := isClosed_range q

/-- Named structure: installing it locally retains the inherited range norm
and supplies the proved completeness, rather than assuming it. -/
def imageCStarAlgebra : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range q) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range q) (h_closed := isClosed_image q)

theorem norm_imageStarAlgEquiv (x : HomKernelQuotient q) :
    ‖imageStarAlgEquiv q x‖ = ‖x‖ := norm_toCodomain q x

theorem isometry_imageStarAlgEquiv : Isometry (imageStarAlgEquiv q) :=
  AddMonoidHomClass.isometry_of_norm (imageStarAlgEquiv q) (norm_imageStarAlgEquiv q)

/-- The same map exposed as a linear isometry equivalence for Banach clients. -/
def imageLinearIsometryEquiv : HomKernelQuotient q ≃ₗᵢ[ℂ] (NonUnitalStarAlgHom.range q) :=
  { toLinearEquiv :=
      { (imageStarAlgEquiv q).toEquiv with
        map_add' := map_add (imageStarAlgEquiv q)
        map_smul' := map_smul (imageStarAlgEquiv q) }
    norm_map' := norm_imageStarAlgEquiv q }

@[simp]
theorem imageLinearIsometryEquiv_apply (x : HomKernelQuotient q) :
    imageLinearIsometryEquiv q x = imageStarAlgEquiv q x := rfl

/-- This equality is about the standard quotient norm, not a newly assigned norm. -/
theorem norm_mk_eq (a : A) : ‖mk q a‖ = ‖q a‖ := (norm_toCodomain q (mk q a)).symm

/-- Every point of the genuine quotient has an EXACT norm-minimizing representative. -/
theorem exists_representative_norm_eq (x : HomKernelQuotient q) :
    ∃ a : A, mk q a = x ∧ ‖a‖ = ‖x‖ := by
  obtain ⟨b, rfl⟩ := mk_surjective q x
  obtain ⟨a, ha, hn⟩ := exists_same_image_norm_eq q b
  exact ⟨a, (mk_eq_mk_iff q a b).2 ha, hn.trans (norm_mk_eq q b).symm⟩

end MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient
