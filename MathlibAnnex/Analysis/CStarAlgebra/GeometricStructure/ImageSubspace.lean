/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SurjectivePreimage
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationComponents
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageWeakDual
import MathlibAnnex.Topology.ClosureSpace.SubspaceMaps
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# The image GSS and the closure of a component

The codomain is the actual subspace `closure (component I)`. Equality of the
component intersection with the representation kernel only identifies this
CLOSURE. It is not used to identify the components themselves. All continuity
here is for the received closure spaces; no topology on S(A) is presumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H)

private def imageSubspaceContinuousMap {B : Type*} [NonUnitalCStarAlgebra B]
    (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

attribute [local instance] HomKernelQuotient.imageCStarAlgebra

/-- Equality of J_C with ker(pi) identifies the closure, NOT necessarily C itself. -/
theorem closure_component_eq_hull_ker
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A)) :
    (NormedSpace.geometricStructureClosure ℂ A).closure
        ((NormedSpace.geometricStructureClosure ℂ A).component I) =
      ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
        ((imageSubspaceContinuousMap pi).ker : Set A) := by
  change ClosureSpace.HullKernel.hull _
    (NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I)) = _
  rw [hI]

/-- Theorem 5.17 for the actual image. Image order and nontriviality are supplied
by proofs inside the definition; neither is an added hypothesis. -/
def imageGeometricStructureHomeomorph (hpi : pi.IsNonzero)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A)) :
    ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi))
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).closure
          ((NormedSpace.geometricStructureClosure ℂ A).component I))) := by
  letI : Nontrivial (NonUnitalStarAlgHom.range pi) := nontrivial_image_of_isNonzero pi hpi
  letI : PartialOrder (NonUnitalStarAlgHom.range pi) := _root_.CStarAlgebra.spectralOrder (NonUnitalStarAlgHom.range pi)
  letI : StarOrderedRing (NonUnitalStarAlgHom.range pi) := _root_.CStarAlgebra.spectralOrderedRing (NonUnitalStarAlgHom.range pi)
  let q := (NonUnitalStarAlgHom.rangeRestrict pi)
  have hq : Function.Surjective q := rangeRestrict_surjective pi
  have hker : ((imageSubspaceContinuousMap q).ker : Set A) =
      ((imageSubspaceContinuousMap pi).ker : Set A) := by
    ext a
    change q a = 0 ↔ pi a = 0
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      change pi a = 0
      exact h
  have htarget : ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
      ((imageSubspaceContinuousMap q).ker : Set A) =
        (NormedSpace.geometricStructureClosure ℂ A).closure
          ((NormedSpace.geometricStructureClosure ℂ A).component I) := by
    rw [hker, closure_component_eq_hull_ker pi I hI]
  exact (geometricStructurePreimageHomeomorph q hq).trans
    ((ClosureSpace.Homeomorph.refl (NormedSpace.geometricStructureClosure ℂ A)).subspace
      _ _ (fun J => Set.ext_iff.mp htarget J))

/-- No choice of an extreme functional enters the action on a GSS point. -/
@[simp]
theorem imageGeometricStructureHomeomorph_val (hpi : pi.IsNonzero)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A))
    (J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi)) :
    ((imageGeometricStructureHomeomorph pi hpi I hI).toEquiv J).val.val =
      (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val := rfl

/-- Every point of the specified component CLOSURE is reached. -/
theorem imageGeometricStructureHomeomorph_surjective (hpi : pi.IsNonzero)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A)) :
    Function.Surjective (imageGeometricStructureHomeomorph pi hpi I hI).toEquiv :=
  (imageGeometricStructureHomeomorph pi hpi I hI).toEquiv.surjective

/-- Forward preservation of every closure in the actual subspace. -/
theorem image_closure_imageGeometricStructureHomeomorph (hpi : pi.IsNonzero)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A))
    (S : Set (NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi))) :
    (imageGeometricStructureHomeomorph pi hpi I hI).toEquiv ''
      (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).closure S =
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).closure
            ((NormedSpace.geometricStructureClosure ℂ A).component I))).closure
          ((imageGeometricStructureHomeomorph pi hpi I hI).toEquiv '' S) :=
  (imageGeometricStructureHomeomorph pi hpi I hI).image_closure S

/-- Reverse preservation of every closure; this is not just a continuous bijection. -/
theorem image_closure_imageGeometricStructureHomeomorph_symm (hpi : pi.IsNonzero)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (hI : NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A I) =
      ((imageSubspaceContinuousMap pi).ker : Set A))
    (S : Set ((NormedSpace.geometricStructureClosure ℂ A).closure
      ((NormedSpace.geometricStructureClosure ℂ A).component I))) :
    (imageGeometricStructureHomeomorph pi hpi I hI).toEquiv.symm ''
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).closure
            ((NormedSpace.geometricStructureClosure ℂ A).component I))).closure S =
      (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).closure
        ((imageGeometricStructureHomeomorph pi hpi I hI).toEquiv.symm '' S) :=
  (imageGeometricStructureHomeomorph pi hpi I hI).symm.image_closure S

/-- The source points can be described using exactly the pulled-back extreme functionals. -/
theorem mem_geometricStructureFamily_range_iff (hpi : pi.IsNonzero) (J : Set (NonUnitalStarAlgHom.range pi)) :
    J ∈ NormedSpace.geometricStructureFamily ℂ (NonUnitalStarAlgHom.range pi) ↔
      ∃ f : StrongDual ℂ (NonUnitalStarAlgHom.range pi),
        f.comp (imageSubspaceContinuousMap (NonUnitalStarAlgHom.rangeRestrict pi)) ∈
          (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∧ (f.ker : Set (NonUnitalStarAlgHom.range pi)) = J := by
  letI : Nontrivial (NonUnitalStarAlgHom.range pi) := nontrivial_image_of_isNonzero pi hpi
  letI : PartialOrder (NonUnitalStarAlgHom.range pi) := _root_.CStarAlgebra.spectralOrder (NonUnitalStarAlgHom.range pi)
  letI : StarOrderedRing (NonUnitalStarAlgHom.range pi) := _root_.CStarAlgebra.spectralOrderedRing (NonUnitalStarAlgHom.range pi)
  rw [mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall]
  exact exists_congr fun f => and_congr
    (comp_mem_extremePoints_dual_closedBall_iff_of_surjective (NonUnitalStarAlgHom.rangeRestrict pi)
      (rangeRestrict_surjective pi) f).symm Iff.rfl

/-- A coefficient seed supplies J_C = ker(pi) by the already received full component theorem. -/
def coefficientImageGeometricStructureHomeomorph (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi))
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).closure
          ((NormedSpace.geometricStructureClosure ℂ A).component
            (matrixCoefficientKernel pi hpi x y hx hy)))) :=
  imageGeometricStructureHomeomorph pi hpi.1 (matrixCoefficientKernel pi hpi x y hx hy)
    (geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel pi hpi x y hx hy)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
