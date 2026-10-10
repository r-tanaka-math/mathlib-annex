/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeMaximalFace
import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic

/-!
# Extreme kernels in the original geometric structure space

The generic geometric structure family is unchanged: its points are unions
of kernels of ALL supporting functionals of maximal proper faces. The C-star
singleton theorem turns such a union into a single extreme-functional kernel,
and maximality of every extreme slice proves the reverse inclusion.

Repeated kernels remain a single point. The parametrization by extreme
functionals is surjective, not claimed injective. These statements concern
the complex algebra, not its real self-adjoint part. Nontriviality is explicit:
for the zero algebra the existing generic family is empty, whereas the dual
ball has the extreme point zero.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

/-- The original union of all supporting kernels is exactly the kernel of the
extreme functional. Both inclusions use the proved entire-family singleton. -/
theorem supportKernelUnion_unitBallSupportFace_eq_ker
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.supportKernelUnion ℂ (NormedSpace.unitBallSupportFace ℂ rho) =
      (rho.ker : Set A) := by
  rw [NormedSpace.supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton
    ℂ _ rho (supportFunctionals_unitBallSupportFace_eq_singleton hrho)]
  ext a
  rfl

/-- Exact family identification with the already defined generic S(A).
No C-star-specific replacement of its definition is introduced. -/
theorem geometricStructureFamily_eq_image_ker_extremePoints_dual_closedBall :
    NormedSpace.geometricStructureFamily ℂ A =
      (fun rho : StrongDual ℂ A => (rho.ker : Set A)) ''
        (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  letI : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  ext I
  constructor
  · rintro ⟨F, hF, hFI⟩
    obtain ⟨rho, hrho, hFrho⟩ :=
      (isMaximalFace_iff_exists_mem_extremePoints_dual_closedBall F).mp hF
    refine ⟨rho, hrho, ?_⟩
    rw [hFrho, supportKernelUnion_unitBallSupportFace_eq_ker hrho] at hFI
    exact hFI
  · rintro ⟨rho, hrho, rfl⟩
    exact ⟨NormedSpace.unitBallSupportFace ℂ rho,
      isMaximalFace_unitBallSupportFace_of_mem_extremePoints_dual_closedBall hrho,
      supportKernelUnion_unitBallSupportFace_eq_ker hrho⟩

/-- Membership in the original family is equivalent to being the kernel of
an extreme functional, with equality of the actual subset of A. -/
theorem mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall
    (I : Set A) : I ∈ NormedSpace.geometricStructureFamily ℂ A ↔
      ∃ rho : StrongDual ℂ A,
        rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∧ (rho.ker : Set A) = I := by
  rw [geometricStructureFamily_eq_image_ker_extremePoints_dual_closedBall]
  rfl

/-- Send an extreme functional to its kernel as a point of the ORIGINAL
geometric structure space. This does not create a new structure space. -/
def extremeKernel (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.GeometricStructureSpace ℂ A :=
  ⟨(rho.val.ker : Set A),
    (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall _).mpr
      ⟨rho.val, rho.property, rfl⟩⟩

@[simp]
theorem coe_extremeKernel (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (extremeKernel rho).val = (rho.val.ker : Set A) := rfl

/-- Every original GSS point is represented by an extreme-functional kernel.
Different functionals may map to the same point. -/
theorem extremeKernel_surjective : Function.Surjective (extremeKernel (A := A)) := by
  intro I
  obtain ⟨rho, hrho, hI⟩ :=
    (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall I.val).mp I.property
  exact ⟨⟨rho, hrho⟩, Subtype.ext hI⟩

end MathlibAnnex.Analysis.CStarAlgebra
