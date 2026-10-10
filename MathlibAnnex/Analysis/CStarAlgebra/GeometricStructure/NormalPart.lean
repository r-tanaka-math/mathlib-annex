/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.ImageSubspace
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.AbsoluteState

/-!
# The normal part of a concrete irreducible C-star algebra

The normal part is a subset of the original general GSS. Its definition uses
literal restrictions of operator coefficients and is independent of a chosen
primitive-ideal label. Closedness and irreducibility are needed for the
component theorem, not smuggled into the definition of the subset.

The component proof reuses the already proved finite-chain/representation
classification. In particular it does not identify components from equality
of primitive kernels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal nonzero-vector coefficient-kernel part of a concrete algebra's GSS. -/
def normalPart (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    Set (NormedSpace.GeometricStructureSpace ℂ S) :=
  {I | ∃ x y : H, x ≠ 0 ∧ y ≠ 0 ∧
    {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} = I.val}

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

private abbrev normalPartCStarAlgebra : NonUnitalCStarAlgebra S :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := inferInstance)

attribute [local instance] normalPartCStarAlgebra

/-- Normalization does not change the set of actual kernels. No irreducibility
is required for this normalization assertion. -/
theorem mem_normalPart_iff_exists_unit_vectors (I : NormedSpace.GeometricStructureSpace ℂ S) :
    I ∈ normalPart S ↔ ∃ x y : H, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} = I.val := by
  constructor
  · rintro ⟨x, y, hx, hy, hI⟩
    obtain ⟨z, w, hz, hw, hker⟩ :=
      NonUnitalCStarRepresentation.exists_unit_vectors_ker_matrixCoefficient_eq
        (NonUnitalStarSubalgebraClass.subtype S) x y hx hy
    exact ⟨z, w, hz, hw,
      (congrArg (fun K : Submodule ℂ S => (K : Set S)) hker).trans hI⟩
  · rintro ⟨x, y, hx, hy, hI⟩
    exact ⟨x, y, norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero),
      norm_ne_zero_iff.mp (by rw [hy]; exact one_ne_zero), hI⟩

/-- Corollary 5.19, strengthened from unit to arbitrary nonzero vectors.
The C-star order is supplied by the fixed spectral-order construction. -/
theorem setOf_inner_apply_eq_zero_mem_geometricStructureFamily
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} ∈
      NormedSpace.geometricStructureFamily ℂ S := by
  letI : Nontrivial S := by
    obtain ⟨a, ha⟩ := hS.1
    refine ⟨⟨a, 0, ?_⟩⟩
    intro h
    subst a
    exact ha (map_zero _)
  letI : PartialOrder S := _root_.CStarAlgebra.spectralOrder S
  letI : StarOrderedRing S := _root_.CStarAlgebra.spectralOrderedRing S
  exact NonUnitalCStarRepresentation.ker_matrixCoefficient_mem_geometricStructureFamily
    (NonUnitalStarSubalgebraClass.subtype S) hS x y hx hy

/-- An actual coefficient seed in S(S), with no choice based solely on a primitive ideal. -/
def restrictedMatrixCoefficientKernel
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) : NormedSpace.GeometricStructureSpace ℂ S :=
  ⟨{a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0},
    setOf_inner_apply_eq_zero_mem_geometricStructureFamily S hS x y hx hy⟩

@[simp]
theorem restrictedMatrixCoefficientKernel_val
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (restrictedMatrixCoefficientKernel S hS x y hx hy).val =
      {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} := rfl

/-- Proposition 6.3 and the component content of Definition 6.4. -/
theorem component_restrictedMatrixCoefficientKernel_eq_normalPart
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ S).component
      (restrictedMatrixCoefficientKernel S hS x y hx hy) = normalPart S := by
  letI : Nontrivial S := by
    obtain ⟨a, ha⟩ := hS.1
    refine ⟨⟨a, 0, ?_⟩⟩
    intro h
    subst a
    exact ha (map_zero _)
  letI : PartialOrder S := _root_.CStarAlgebra.spectralOrder S
  letI : StarOrderedRing S := _root_.CStarAlgebra.spectralOrderedRing S
  have hseed : restrictedMatrixCoefficientKernel S hS x y hx hy =
      NonUnitalCStarRepresentation.matrixCoefficientKernel
        (NonUnitalStarSubalgebraClass.subtype S) hS x y hx hy := Subtype.ext rfl
  rw [hseed, NonUnitalCStarRepresentation.component_matrixCoefficientKernel_eq_family]
  ext I
  constructor
  · rintro ⟨z, w, hz, hw, heq⟩
    exact ⟨z, w, hz, hw, congrArg Subtype.val heq⟩
  · rintro ⟨z, w, hz, hw, heq⟩
    exact ⟨z, w, hz, hw, Subtype.ext heq⟩

section Image

variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

private def normalPartContinuousMap {B : Type*} [NonUnitalCStarAlgebra B]
    (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- Corollary 5.18 for the actual image, again allowing all nonzero vectors. -/
theorem setOf_inner_apply_eq_zero_mem_geometricStructureFamily_range
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    {a : (NonUnitalStarAlgHom.range pi) | inner ℂ y ((a : H →L[ℂ] H) x) = 0} ∈
      NormedSpace.geometricStructureFamily ℂ (NonUnitalStarAlgHom.range pi) :=
  setOf_inner_apply_eq_zero_mem_geometricStructureFamily (NonUnitalStarAlgHom.range pi)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi) x y hx hy

/-- The normal part corresponds to the component of a COEFFICIENT seed.
Equality of representation kernels alone is not used to select this component. -/
theorem image_normalPart_eq_component
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (fun J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi) =>
      ((NonUnitalCStarRepresentation.coefficientImageGeometricStructureHomeomorph
        pi hpi x y hx hy).toEquiv J).val) '' normalPart (NonUnitalStarAlgHom.range pi) =
      (NormedSpace.geometricStructureClosure ℂ A).component
        (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy) := by
  let h := NonUnitalCStarRepresentation.coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy
  have hpoint (J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi))
      (z w : H) (hz : z ≠ 0) (hw : w ≠ 0)
      (hJ : {a : (NonUnitalStarAlgHom.range pi) | inner ℂ w ((a : H →L[ℂ] H) z) = 0} = J.val) :
      (h.toEquiv J).val = NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi z w hz hw := by
    apply Subtype.ext
    change (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val =
      ((NonUnitalCStarRepresentation.matrixCoefficient pi z w).ker : Set A)
    rw [← hJ]
    rfl
  ext I
  constructor
  · rintro ⟨J, ⟨z, w, hz, hw, hJ⟩, rfl⟩
    have hm := congrArg
      (fun F : Set (NormedSpace.GeometricStructureSpace ℂ A) => (h.toEquiv J).val ∈ F)
      (NonUnitalCStarRepresentation.component_matrixCoefficientKernel_eq_family pi hpi x y hx hy)
    apply Eq.mpr hm
    exact ⟨z, w, hz, hw, (hpoint J z w hz hw hJ).symm⟩
  · intro hI
    rw [NonUnitalCStarRepresentation.component_matrixCoefficientKernel_eq_family] at hI
    obtain ⟨z, w, hz, hw, rfl⟩ := hI
    let J := restrictedMatrixCoefficientKernel (NonUnitalStarAlgHom.range pi)
      ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi) z w hz hw
    exact ⟨J, ⟨z, w, hz, hw, rfl⟩, hpoint J z w hz hw rfl⟩

/-- Proposition 6.1 in its literal image-restriction/pullback form.
The Hilbert space and representation are the genuine GNS of the pure state. -/
theorem component_pureStateKernel_eq_setOf_exists_image_unit_coefficients
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    (NormedSpace.geometricStructureClosure ℂ A).component
      (extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩) =
      {I : NormedSpace.GeometricStructureSpace ℂ A |
        ∃ x y : NonUnitalStateGNS.Space phi hpure.1, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
          (((NonUnitalCStarRepresentation.matrixCoefficient
              (NonUnitalCStarRepresentation.imageRepresentation
                (NonUnitalStateGNS.representation phi hpure.1)) x y).comp
            (normalPartContinuousMap (NonUnitalStarAlgHom.rangeRestrict
              (NonUnitalStateGNS.representation phi hpure.1)))).ker : Set A) = I.val} := by
  exact component_pureStateKernel_eq_setOf_exists_unit_vectors phi hpure

end Image
end MathlibAnnex.Analysis.CStarAlgebra
