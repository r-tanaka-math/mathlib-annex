/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPart

/-!
# The image normal part and the original coefficient component

Restrict the image-GSS homeomorphism only AFTER proving that the normal part
corresponds to the component of its coefficient seed. The target is the direct
subspace of S(A), not an unconnected nested subtype of the component closure.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
variable (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- The canonical restriction to the normal part, with both directions continuous
for the ORIGINAL subspace closures. -/
def imageNormalPartHomeomorph :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi)))
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component
          (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy))) := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let d := NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)
  let C := c.component (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy)
  let Z := c.closure C
  let N := normalPart (NonUnitalStarAlgHom.range pi)
  let h := NonUnitalCStarRepresentation.coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy
  let F : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi) →
      NormedSpace.GeometricStructureSpace ℂ A := fun J => (h.toEquiv J).val
  have hF : Function.Injective F := by
    intro J L heq
    apply h.toEquiv.injective
    exact Subtype.ext heq
  have hrange : F '' N = C := image_normalPart_eq_component pi hpi x y hx hy
  have hchar (J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi)) : J ∈ N ↔ F J ∈ C := by
    constructor
    · intro hJ
      rw [← hrange]
      exact ⟨J, hJ, rfl⟩
    · intro hJ
      rw [← hrange] at hJ
      obtain ⟨L, hL, hLJ⟩ := hJ
      exact hF hLJ ▸ hL
  let inclusion : C → Z := fun I => ⟨I.val, c.subset_closure C I.property⟩
  let e : N ≃ C :=
    { toFun J := ⟨F J.val, (hchar J.val).1 J.property⟩
      invFun I := ⟨h.toEquiv.symm (inclusion I), (hchar _).2 (by
        change (h.toEquiv (h.toEquiv.symm (inclusion I))).val ∈ C
        simpa only [h.toEquiv.apply_symm_apply] using I.property)⟩
      left_inv J := by
        apply Subtype.ext
        apply h.toEquiv.injective
        rw [h.toEquiv.apply_symm_apply]
      right_inv I := by
        apply Subtype.ext
        change F (h.toEquiv.symm (inclusion I)) = I.val
        exact congrArg Subtype.val (h.toEquiv.apply_symm_apply (inclusion I)) }
  refine { toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (ClosureSpace.continuous_induced_iff (d.subspace N) c Subtype.val e).2
    exact ((ClosureSpace.continuous_subtype_val c Z).comp h.continuous_toFun).comp
      (ClosureSpace.continuous_subtype_val d N)
  · apply (ClosureSpace.continuous_induced_iff (c.subspace C) d Subtype.val e.symm).2
    exact h.continuous_invFun.comp (ClosureSpace.continuous_inclusion c (c.subset_closure C))

/-- On underlying sets this restriction is still literal inverse image. -/
@[simp]
theorem imageNormalPartHomeomorph_val (J : normalPart (NonUnitalStarAlgHom.range pi)) :
    ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv J).val.val =
      (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val.val := rfl

/-- Every closure in the normal part is transported exactly. -/
theorem image_closure_imageNormalPartHomeomorph (S : Set (normalPart (NonUnitalStarAlgHom.range pi))) :
    (imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv ''
        ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))).closure S =
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component
          (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy))).closure
        ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv '' S) :=
  (imageNormalPartHomeomorph pi hpi x y hx hy).image_closure S

/-- Every closure is also transported by the inverse restriction. -/
theorem image_closure_imageNormalPartHomeomorph_symm
    (S : Set ((NormedSpace.geometricStructureClosure ℂ A).component
      (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy))) :
    (imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv.symm ''
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component
            (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy))).closure S =
      ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))).closure
        ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv.symm '' S) :=
  (imageNormalPartHomeomorph pi hpi x y hx hy).symm.image_closure S

end MathlibAnnex.Analysis.CStarAlgebra
