/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.AffineSlice

/-!
# Affine slices are the existing maximal support faces

Common supports need not be unique. When two such supports take value one
at the same unit vector, their value-one faces agree: the phase is constant
on a convex sphere set. A functional witnessing membership in the kernel
union is normalized at that vector to prove the forward slice inclusion.

The reverse inclusion only uses the kernel of the selected functional.
No convexity or linearity of the entire kernel union is postulated.
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

/-- A common support's value-one face is contained in its maximal filter. -/
theorem IsMaximalBirkhoffJamesFilter.unitBallSupportFace_subset
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f : StrongDual 𝕜 E}
    (hf : ∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u) :
    unitBallSupportFace 𝕜 f ⊆ U := by
  rw [hU.eq_absoluteNormAttainmentSet 𝕜 hf]
  exact unitBallSupportFace_subset_absoluteNormAttainmentSet 𝕜
    (hf 0 (hU.1.zero_mem 𝕜)).1

/-- The two value-one faces agree after normalizing both common supports at
one unit vector. This is equality of faces, not uniqueness of supports. -/
theorem IsMaximalBirkhoffJamesFilter.unitBallSupportFace_eq_of_common_apply_eq_one
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f g : StrongDual 𝕜 E}
    (hf : ∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u)
    (hg : ∀ u ∈ U, g ∈ absoluteNormingFunctionals 𝕜 u)
    {x : E} (hx : ‖x‖ = 1) (hfx : f x = 1) (hgx : g x = 1) :
    unitBallSupportFace 𝕜 f = unitBallSupportFace 𝕜 g := by
  have hxne : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  letI : Nontrivial E := ⟨⟨x, 0, hxne⟩⟩
  have hF := hU.isMaximalFace_unitBallSupportFace 𝕜 hf
  have hFU := hU.unitBallSupportFace_subset 𝕜 hf
  have hxF : x ∈ unitBallSupportFace 𝕜 f := ⟨mem_closedBall_zero_iff.mpr hx.le, hfx⟩
  have hgF : ∀ z ∈ unitBallSupportFace 𝕜 f, g z = 1 :=
    eq_one_on_convex_of_norm_apply_eq_one 𝕜 hF.convex
      (fun z hz => (hg z (hFU hz)).2.trans ((by simpa [Metric.mem_sphere] using hF.subset_sphere hz)))
      hxF hgx
  exact hF.eq_unitBallSupportFace 𝕜 ⟨(hg 0 (hU.1.zero_mem 𝕜)).1, hgF⟩

/-- The slice is exactly the existing value-one face of any common support
normalized at its unit base point. Both inclusions are proved as set inclusions. -/
theorem IsMaximalBirkhoffJamesFilter.affineSlice_eq_unitBallSupportFace
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1)
    {f : StrongDual 𝕜 E} (hf : ∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u)
    (hfx : f x = 1) :
    birkhoffJamesAffineSlice 𝕜 U x = unitBallSupportFace 𝕜 f := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨g, hg, hgdiff⟩ :=
      (mem_birkhoffJamesKernel_iff_exists_common_absoluteNormingFunctional 𝕜
        (hU.1.nonempty 𝕜) (fun u hu v hv => hU.1.directed 𝕜 hu hv) (z - x)).mp hz.2
    have hgweak : g.toWeakDual ∈ weakStarCommonAbsoluteNormingFunctionals 𝕜 U :=
      (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr hg
    have hgxabs : g ∈ absoluteNormingFunctionals 𝕜 x :=
      hU.weakStarCommonAbsoluteNormingFunctionals_subset_of_affineSlice_subset_sphere
        𝕜 hx hslice hgweak
    have hgxnorm : ‖g x‖ = 1 := hgxabs.2.trans hx
    have hgxne : g x ≠ 0 := norm_ne_zero_iff.mp (hgxnorm.trans_ne one_ne_zero)
    have hgz : g z = g x := sub_eq_zero.mp (by simpa only [map_sub] using hgdiff)
    let g₀ : StrongDual 𝕜 E := (g x)⁻¹ • g
    have ha : ‖(g x)⁻¹‖ = 1 := by rw [norm_inv, hgxnorm, inv_one]
    have hg₀ : ∀ u ∈ U, g₀ ∈ absoluteNormingFunctionals 𝕜 u :=
      fun u hu => smul_mem_absoluteNormingFunctionals 𝕜 ha (hg u hu)
    have hg₀x : g₀ x = 1 := inv_mul_cancel₀ hgxne
    have hzG : z ∈ unitBallSupportFace 𝕜 g₀ := by
      refine ⟨hz.1, ?_⟩
      change (g x)⁻¹ * g z = 1
      rw [hgz, inv_mul_cancel₀ hgxne]
    have hfaces := hU.unitBallSupportFace_eq_of_common_apply_eq_one 𝕜 hf hg₀ hx hfx hg₀x
    exact hfaces.symm ▸ hzG
  · intro z hz
    refine ⟨hz.1, ?_⟩
    intro u hu
    apply birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero 𝕜 (hf u hu)
    rw [map_sub, hz.2, hfx, sub_self]

/-- An actual common support is selected and normalized. Its face is exactly
the slice; no chosen-support uniqueness is required. -/
theorem IsMaximalBirkhoffJamesFilter.exists_affineSlice_eq_unitBallSupportFace
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    ∃ f : StrongDual 𝕜 E, (∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u) ∧
      f x = 1 ∧ birkhoffJamesAffineSlice 𝕜 U x = unitBallSupportFace 𝕜 f := by
  obtain ⟨g, hg⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
  have hgweak : g.toWeakDual ∈ weakStarCommonAbsoluteNormingFunctionals 𝕜 U :=
    (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr hg
  have hgxabs : g ∈ absoluteNormingFunctionals 𝕜 x :=
    hU.weakStarCommonAbsoluteNormingFunctionals_subset_of_affineSlice_subset_sphere
      𝕜 hx hslice hgweak
  have hgxnorm : ‖g x‖ = 1 := hgxabs.2.trans hx
  have hgxne : g x ≠ 0 := norm_ne_zero_iff.mp (hgxnorm.trans_ne one_ne_zero)
  let f : StrongDual 𝕜 E := (g x)⁻¹ • g
  have ha : ‖(g x)⁻¹‖ = 1 := by rw [norm_inv, hgxnorm, inv_one]
  have hf : ∀ u ∈ U, f ∈ absoluteNormingFunctionals 𝕜 u :=
    fun u hu => smul_mem_absoluteNormingFunctionals 𝕜 ha (hg u hu)
  have hfx : f x = 1 := inv_mul_cancel₀ hgxne
  exact ⟨f, hf, hfx, hU.affineSlice_eq_unitBallSupportFace 𝕜 hx hslice hf hfx⟩

/-- The independent maximality conclusion of Lemma 4.9. -/
theorem IsMaximalBirkhoffJamesFilter.isMaximalFace_affineSlice
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {x : E} (hx : ‖x‖ = 1)
    (hslice : birkhoffJamesAffineSlice 𝕜 U x ⊆ sphere (0 : E) 1) :
    IsMaximalFace (birkhoffJamesAffineSlice 𝕜 U x) := by
  have hxne : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  letI : Nontrivial E := ⟨⟨x, 0, hxne⟩⟩
  obtain ⟨f, hf, _, hface⟩ := hU.exists_affineSlice_eq_unitBallSupportFace 𝕜 hx hslice
  rw [hface]
  exact hU.isMaximalFace_unitBallSupportFace 𝕜 hf

end NormedSpace
