/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation

/-!
# The actual inclusion representation of a representation image

The range is the literal non-unital star subalgebra. Its C-star structure is
installed from the already proved norm-closedness. The original representation
factors as the range restriction followed by this inclusion, and surjectivity
reflects both nonzeroness and irreducibility.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H)

local instance : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- Inclusion of the actual closed image into the operators on the original Hilbert space. -/
def imageRepresentation : NonUnitalCStarRepresentation (NonUnitalStarAlgHom.range pi) H :=
  NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)

@[simp]
theorem imageRepresentation_apply (a : (NonUnitalStarAlgHom.range pi)) : imageRepresentation pi a = a.val := rfl

@[simp]
theorem imageRepresentation_comp_rangeRestrict :
    (imageRepresentation pi).comp (NonUnitalStarAlgHom.rangeRestrict pi) = pi := by ext a; rfl

/-- The original algebra surjects onto this image, including in the non-unital case. -/
theorem rangeRestrict_surjective : Function.Surjective (NonUnitalStarAlgHom.rangeRestrict pi) := by
  intro b
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1 b.property
  exact ⟨a, Subtype.ext ha⟩

/-- This nontriviality is derived from the ACTUAL nonzero representation. -/
theorem nontrivial_image_of_isNonzero (hpi : pi.IsNonzero) : Nontrivial (NonUnitalStarAlgHom.range pi) := by
  obtain ⟨a, ha⟩ := hpi
  refine ⟨⟨(NonUnitalStarAlgHom.rangeRestrict pi) a, 0, ?_⟩⟩
  intro hz
  exact ha (congrArg Subtype.val hz)

theorem isNonzero_imageRepresentation_iff :
    (imageRepresentation pi).IsNonzero ↔ pi.IsNonzero := by
  have h := isNonzero_comp_iff_of_surjective (imageRepresentation pi)
    (NonUnitalStarAlgHom.rangeRestrict pi) (rangeRestrict_surjective pi)
  rw [imageRepresentation_comp_rangeRestrict] at h
  exact h.symm

/-- The image inclusion is irreducible precisely when the original representation is. -/
theorem isIrreducible_imageRepresentation_iff :
    (imageRepresentation pi).IsIrreducible ↔ pi.IsIrreducible := by
  have h := isIrreducible_comp_iff_of_surjective (imageRepresentation pi)
    (NonUnitalStarAlgHom.rangeRestrict pi) (rangeRestrict_surjective pi)
  rw [imageRepresentation_comp_rangeRestrict] at h
  exact h.symm

/-- Restriction of a full-operator coefficient to the image is its literal coefficient. -/
@[simp]
theorem matrixCoefficient_imageRepresentation_apply (x y : H) (a : (NonUnitalStarAlgHom.range pi)) :
    matrixCoefficient (imageRepresentation pi) x y a = inner ℂ y ((a : H →L[ℂ] H) x) := rfl

private def imageRestrictionContinuousMap : A →L[ℂ] (NonUnitalStarAlgHom.range pi) :=
  LinearMap.mkContinuous
    { toFun := NonUnitalStarAlgHom.rangeRestrict pi,
      map_add' := map_add (NonUnitalStarAlgHom.rangeRestrict pi),
      map_smul' := map_smul (NonUnitalStarAlgHom.rangeRestrict pi) }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- Pulling the restricted coefficient back gives the ORIGINAL coefficient. -/
theorem matrixCoefficient_imageRepresentation_comp (x y : H) :
    (matrixCoefficient (imageRepresentation pi) x y).comp
        (imageRestrictionContinuousMap pi) = matrixCoefficient pi x y := by
  ext a
  rfl

/-- Set-level kernel transport, without conflating the representation and scalar kernels. -/
theorem preimage_ker_matrixCoefficient_imageRepresentation (x y : H) :
    (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' ((matrixCoefficient (imageRepresentation pi) x y).ker : Set (NonUnitalStarAlgHom.range pi)) =
      ((matrixCoefficient pi x y).ker : Set A) := rfl

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
