/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientComponents

/-!
# The coefficient-kernel family of one irreducible representation

The nonzero-vector and unit-vector descriptions agree as actual GSS subsets.
The family lies inside one of the received finite-chain components, and its
kernel intersection is the kernel of the representation. The reverse
component inclusion is deliberately not asserted here: it needs the still
separate inequivalent-pair closedness argument of Paper 5.8.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def coefficientFamilyContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The actual GSS kernel points represented by one nonzero irreducible representation. -/
def matrixCoefficientKernelFamily (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    Set (NormedSpace.GeometricStructureSpace ℂ A) :=
  {I | ∃ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0), matrixCoefficientKernel pi hpi x y hx hy = I}

/-- Unit vectors give exactly the same family; normalization does not add labels. -/
theorem mem_matrixCoefficientKernelFamily_iff_exists_unit_vectors
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    I ∈ matrixCoefficientKernelFamily pi hpi ↔
      ∃ x y : H, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ((matrixCoefficient pi x y).ker : Set A) = I.val := by
  constructor
  · rintro ⟨x, y, hx, hy, hI⟩
    obtain ⟨v, w, hv, hw, hker⟩ := exists_unit_vectors_ker_matrixCoefficient_eq pi x y hx hy
    refine ⟨v, w, hv, hw, ?_⟩
    exact (congrArg (fun P : Submodule ℂ A => (P : Set A)) hker).trans
      (congrArg Subtype.val hI)
  · rintro ⟨x, y, hx, hy, hI⟩
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
    have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; exact one_ne_zero)
    exact ⟨x, y, hx0, hy0, Subtype.ext hI⟩

/-- The family is contained in the actual component of any one of its points. -/
theorem matrixCoefficientKernelFamily_subset_component
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    matrixCoefficientKernelFamily pi hpi ⊆
      (NormedSpace.geometricStructureClosure ℂ A).component
        (matrixCoefficientKernel pi hpi x y hx hy) := by
  rintro I ⟨z, w, hz, hw, rfl⟩
  exact related_matrixCoefficientKernel pi hpi x y z w hx hy hz hw

/-- Intersection of the coefficient-kernel FAMILY is precisely ker(pi).
This does not replace the family by an entire component without proof. -/
theorem setOf_forall_mem_matrixCoefficientKernelFamily_eq_ker
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    {a : A | ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      I ∈ matrixCoefficientKernelFamily pi hpi → a ∈ I.val} =
        ((coefficientFamilyContinuousMap pi).ker : Set A) := by
  ext a
  constructor
  · intro ha
    change pi a = 0
    ext x
    by_cases hx : x = 0
    · simp [hx]
    by_contra hax
    have hx0 : pi a x ≠ 0 := by simpa only [ContinuousLinearMap.zero_apply] using hax
    let I := matrixCoefficientKernel pi hpi x (pi a x) hx hx0
    have hIa : a ∈ I.val := ha I ⟨x, pi a x, hx, hx0, rfl⟩
    have hinner : inner ℂ (pi a x) (pi a x) = 0 := hIa
    exact hx0 (inner_self_eq_zero.mp hinner)
  · intro ha
    change pi a = 0 at ha
    rintro I ⟨x, y, hx, hy, rfl⟩
    change inner ℂ y (pi a x) = 0
    simp only [ha, ContinuousLinearMap.zero_apply, inner_zero_right]

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
