/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterAntichain
public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarCommonAbsoluteSupport

/-!
# Affine slices of Birkhoff--James filter kernels

The slice is a translate of a *set* intersected with the primal ball.
The kernel set is not regarded as a submodule. Linear reasoning is confined
to the kernel of one actual common supporting functional at a time.

The independent conclusion of JMAA 514 (2022), Lemma 4.8, is obtained from
the previously proved operator-norm criterion for absolute norm attainment.
This is an alternative to the paper's distance/Hahn--Banach calculation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The affine slice `(x + I_U) ∩ B_E`, expressed using membership of a
vector difference in the existing set-valued filter kernel. -/
def birkhoffJamesAffineSlice (U : Set E) (x : E) : Set E :=
  {z ∈ closedBall (0 : E) 1 | z - x ∈ birkhoffJamesKernel 𝕜 U}

@[simp]
theorem mem_birkhoffJamesAffineSlice {U : Set E} {x z : E} :
    z ∈ birkhoffJamesAffineSlice 𝕜 U x ↔
      z ∈ closedBall (0 : E) 1 ∧ z - x ∈ birkhoffJamesKernel 𝕜 U := Iff.rfl

/-- The difference-membership definition is exactly the usual translated-set slice. -/
theorem birkhoffJamesAffineSlice_eq_image_add_inter (U : Set E) (x : E) :
    birkhoffJamesAffineSlice 𝕜 U x =
      (fun y => x + y) '' birkhoffJamesKernel 𝕜 U ∩ closedBall (0 : E) 1 := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨z - x, hz.2, by abel⟩, hz.1⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    exact ⟨hz, by simpa only [add_sub_cancel_left] using hy⟩

theorem self_mem_birkhoffJamesAffineSlice {U : Set E} {x : E} (hx : ‖x‖ ≤ 1) :
    x ∈ birkhoffJamesAffineSlice 𝕜 U x :=
  ⟨mem_closedBall_zero_iff.mpr hx, by
    rw [sub_self]
    exact zero_mem_birkhoffJamesKernel 𝕜 U⟩

/-- A unit scalar multiple of an absolute norming functional is again absolute
norming. This changes a phase, not the supporting-functional family. -/
theorem smul_mem_absoluteNormingFunctionals {f : StrongDual 𝕜 E} {x : E} {a : 𝕜}
    (ha : ‖a‖ = 1) (hf : f ∈ absoluteNormingFunctionals 𝕜 x) :
    a • f ∈ absoluteNormingFunctionals 𝕜 x := by
  refine ⟨?_, ?_⟩
  · simpa only [norm_smul, ha, one_mul] using hf.1
  · change ‖a * f x‖ = ‖x‖
    rw [norm_mul, ha, one_mul, hf.2]

/-- The affine condition forces every norm-one common support to attain its
norm at the base point. Only an individual functional kernel is used linearly. -/
theorem mem_absoluteNormingFunctionals_of_affineSlice_subset_sphere
    {U : Set E} {x : E} {f : StrongDual 𝕜 E} (hfnorm : ‖f‖ = 1)
    (hf : ∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u) (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    f ∈ absoluteNormingFunctionals 𝕜 x := by
  apply mem_absoluteNormingFunctionals_of_kernel_subset 𝕜 hfnorm
  intro y hfy a
  rw [hx]
  by_contra h
  have hsmall : ‖x + a • y‖ < 1 := lt_of_not_ge h
  have hay : a • y ∈ birkhoffJamesKernel 𝕜 U := by
    intro u hu
    apply birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero
      𝕜 (hf u hu)
    simp only [map_smul, hfy, smul_zero]
  have hz : x + a • y ∈ birkhoffJamesAffineSlice 𝕜 U x :=
    ⟨mem_closedBall_zero_iff.mpr hsmall.le, by
      simpa only [add_sub_cancel_left] using hay⟩
  exact hsmall.ne (by simpa only [Metric.mem_sphere, dist_zero_right] using hslice hz)

end NormedSpace

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Lemma 4.8 in its actual weak-star carrier: every common absolute support
norms the unit base point whenever the affine slice stays on the sphere.
Nontriviality is derived from that point rather than imposed separately. -/
theorem IsMaximalBirkhoffJamesFilter.weakStarCommonAbsoluteNormingFunctionals_subset_of_affineSlice_subset_sphere
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    weakStarCommonAbsoluteNormingFunctionals 𝕜 U ⊆ weakStarAbsoluteNormingFunctionals 𝕜 x := by
  have hxne : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  letI : Nontrivial E := ⟨⟨x, 0, hxne⟩⟩
  intro f hf
  have hfU := (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mp hf
  exact mem_absoluteNormingFunctionals_of_affineSlice_subset_sphere 𝕜
    (hU.norm_eq_one 𝕜 hfU) hfU hx hslice

end NormedSpace
