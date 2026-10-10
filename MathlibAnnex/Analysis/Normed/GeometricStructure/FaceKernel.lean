/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.ConvexFilter
public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarAbsoluteSupport

/-!
# Intersection kernels and the original face kernel

For every nonempty real-convex sphere set, the intersection of right
orthogonality sets equals the original union of kernels of common supports.
The forward direction first uses weak-star compactness to obtain one common
absolute support, and then normalizes its phase on the entire convex set.
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

theorem birkhoffJamesKernel_eq_supportKernelUnion {C : Set E} (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hsphere : C ⊆ sphere (0 : E) 1) :
    birkhoffJamesKernel 𝕜 C = supportKernelUnion 𝕜 C := by
  ext y
  constructor
  · intro hy
    obtain ⟨f, hf, hfy⟩ :=
      (mem_birkhoffJamesKernel_iff_exists_common_absoluteNormingFunctional 𝕜 hne
        (directed_birkhoffJamesOrthogonalSet_of_convex_subset_sphere 𝕜 hconv hsphere) y).mp hy
    obtain ⟨a, _, haf⟩ := exists_norm_eq_one_smul_mem_supportFunctionals 𝕜 hne hconv hsphere hf
    refine ⟨a • f, haf, ?_⟩
    change a * f y = 0
    rw [hfy, mul_zero]
  · rintro ⟨f, hf, hfy⟩ x hx
    apply birkhoffJamesOrthogonal_of_mem_normingFunctionals_apply_eq_zero 𝕜 _ hfy
    have hxnorm : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hx
    refine ⟨hf.1, ?_⟩
    simpa only [hxnorm, algebraMap.coe_one] using hf.2 x hx

/-- A supporting functional remains absolutely norming on all scalar multiples
of its value-one face. -/
theorem unitBallSupportFace_subset_absoluteNormAttainmentSet {f : StrongDual 𝕜 E}
    (hf : ‖f‖ ≤ 1) : unitBallSupportFace 𝕜 f ⊆ absoluteNormAttainmentSet 𝕜 f := by
  intro x hx
  change ‖f x‖ = ‖x‖
  have hxnorm : ‖x‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      unitBallSupportFace_subset_sphere 𝕜 hf hx
  rw [hx.2, norm_one, hxnorm]

/-- The absolute norm-attainment set and its value-one face have the same
intersection kernel. The zero vector is dealt with explicitly. -/
theorem birkhoffJamesKernel_absoluteNormAttainmentSet {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) :
    birkhoffJamesKernel 𝕜 (absoluteNormAttainmentSet 𝕜 f) =
      birkhoffJamesKernel 𝕜 (unitBallSupportFace 𝕜 f) := by
  apply Subset.antisymm
  · exact birkhoffJamesKernel_antitone 𝕜 (unitBallSupportFace_subset_absoluteNormAttainmentSet 𝕜 hf)
  · intro y hy x hx
    by_cases hx₀ : x = 0
    · subst x
      exact birkhoffJamesOrthogonal_zero_left y
    have hfx : f x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne (norm_ne_zero_iff.mpr hx₀))
    have h := hy ((f x)⁻¹ • x) (inv_apply_smul_mem_unitBallSupportFace 𝕜 ⟨hf, hx⟩ hx₀)
    simpa only [smul_smul, mul_inv_cancel₀ hfx, one_smul] using h.smul (f x) 1

end NormedSpace
