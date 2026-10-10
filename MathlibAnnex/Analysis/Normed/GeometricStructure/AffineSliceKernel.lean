/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.AffineSliceFace

/-!
# Recovering a filter kernel from its affine slice

JMAA 514 (2022), Theorem 4.10, recovers `I_U` as the INTERSECTION of the
right-orthogonality sets indexed by the slice. It is not their union.
The separate union formula below is a union of kernels of common supporting
functionals, indexed by the existing `supportFunctionals` of the slice.

All objects here remain sets. Neither formula treats `I_U` as a submodule.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The independent affine-slice reconstruction theorem, using the existing
intersection-kernel operation on both sides. -/
theorem IsMaximalBirkhoffJamesFilter.kernel_affineSlice
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    birkhoffJamesKernel 𝕜 (birkhoffJamesAffineSlice 𝕜 U x) = birkhoffJamesKernel 𝕜 U := by
  obtain ⟨f, hf, _, hface⟩ := hU.exists_affineSlice_eq_unitBallSupportFace 𝕜 hx hslice
  calc
    birkhoffJamesKernel 𝕜 (birkhoffJamesAffineSlice 𝕜 U x) =
        birkhoffJamesKernel 𝕜 (unitBallSupportFace 𝕜 f) := congrArg _ hface
    _ = birkhoffJamesKernel 𝕜 (absoluteNormAttainmentSet 𝕜 f) :=
      (birkhoffJamesKernel_absoluteNormAttainmentSet 𝕜 (hf 0 (hU.1.zero_mem 𝕜)).1).symm
    _ = birkhoffJamesKernel 𝕜 U := congrArg _ (hU.eq_absoluteNormAttainmentSet 𝕜 hf).symm

/-- The literal intersection in the printed statement of Theorem 4.10. -/
theorem IsMaximalBirkhoffJamesFilter.kernel_eq_iInter_affineSlice
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    birkhoffJamesKernel 𝕜 U =
      ⋂ z ∈ birkhoffJamesAffineSlice 𝕜 U x, birkhoffJamesOrthogonalSet 𝕜 z := by
  rw [← hU.kernel_affineSlice 𝕜 hx hslice]
  ext y
  simp only [mem_birkhoffJamesKernel, mem_iInter, birkhoffJamesOrthogonalSet, mem_setOf_eq]

/-- The same set has a different, valid UNION description: a union of the
kernels of the slice's common supports, not a union of right-orthogonality sets. -/
theorem IsMaximalBirkhoffJamesFilter.kernel_eq_iUnion_supportFunctionals_affineSlice
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    birkhoffJamesKernel 𝕜 U =
      ⋃ f ∈ supportFunctionals 𝕜 (birkhoffJamesAffineSlice 𝕜 U x),
        (f : E → 𝕜) ⁻¹' {0} := by
  have hF := hU.isMaximalFace_affineSlice 𝕜 hx hslice
  calc
    birkhoffJamesKernel 𝕜 U = birkhoffJamesKernel 𝕜 (birkhoffJamesAffineSlice 𝕜 U x) :=
      (hU.kernel_affineSlice 𝕜 hx hslice).symm
    _ = supportKernelUnion 𝕜 (birkhoffJamesAffineSlice 𝕜 U x) :=
      birkhoffJamesKernel_eq_supportKernelUnion 𝕜 hF.nonempty hF.convex hF.subset_sphere
    _ = _ := supportKernelUnion_eq_iUnion 𝕜 _

end NormedSpace
