import MathlibAnnex.Analysis.Normed.Sphere.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Radial extension of an isometry between unit spheres

Let `e` be a bijective isometry between the unit spheres of two real normed spaces.
This file extends `e` radially by

`x ↦ ‖x‖ • e (NormedSpace.normalize x)`

away from the origin, and sends the origin to the origin.  The extension preserves
norms, agrees with `e` on the unit sphere, and is a homeomorphism whose forward and
inverse maps are both `3`-Lipschitz.

The public input type is Mathlib's sphere subtype
`Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1`.  The scalar field is
intentionally `ℝ`: no complex-scalar generalization is asserted here.  The radial
extension is generally nonlinear and is not asserted to be an isometry of the
ambient spaces.  The constant `3` is a certified bound, not an optimality claim.
-/

noncomputable section

open Set Metric Function
open scoped NNReal

namespace MathlibAnnex
namespace Sphere

universe u v

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
@[simp] private theorem sphere_norm_image
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    (u : Metric.sphere (0 : X) 1) :
    ‖(e u : Y)‖ = 1 := norm_eq_of_mem_sphere (e u)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
private theorem sphere_norm_sub_image
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    (u v : Metric.sphere (0 : X) 1) :
    ‖(e u : Y) - (e v : Y)‖ = ‖(u : X) - (v : X)‖ := by
  have hY : dist (e u : Y) (e v : Y) = dist u v := by
    simpa only [Function.comp_apply] using
      (((isometry_subtype_coe :
          Isometry ((↑) : Metric.sphere (0 : Y) 1 → Y)).comp e.isometry).dist_eq u v)
  have hX : dist (u : X) (v : X) = dist u v :=
    (isometry_subtype_coe :
      Isometry ((↑) : Metric.sphere (0 : X) 1 → X)).dist_eq u v
  calc
    ‖(e u : Y) - (e v : Y)‖ = dist (e u : Y) (e v : Y) :=
      (dist_eq_norm _ _).symm
    _ = dist u v := hY
    _ = dist (u : X) (v : X) := hX.symm
    _ = ‖(u : X) - (v : X)‖ := dist_eq_norm _ _

omit [NormedSpace ℝ X] in
private theorem abs_norm_sub_le_norm_sub (x y : X) :
    |‖x‖ - ‖y‖| ≤ ‖x - y‖ := by
  refine abs_sub_le_iff.mpr ⟨norm_sub_norm_le x y, ?_⟩
  simpa only [norm_sub_rev] using (norm_sub_norm_le y x)

/-- The angular part of the radial estimate.  The smaller radius multiplies the
change of normalized directions, producing a bound by twice the ambient chord. -/
theorem scaled_normalize_dist_le_two
    {x y : X} (hx : x ≠ 0) (hy : y ≠ 0) (hyx : ‖y‖ ≤ ‖x‖) :
    ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      2 * ‖x - y‖ := by
  let q : ℝ := ‖y‖ / ‖x‖
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 ≤ ‖y‖ := norm_nonneg y
  have hq0 : 0 ≤ q := div_nonneg hny hnx.le
  have hq1 : q ≤ 1 := (div_le_one hnx).2 hyx
  have hqnx : q * ‖x‖ = ‖y‖ := by
    dsimp [q]
    field_simp [ne_of_gt hnx]
  have hscaled :
      ‖y‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
        q • x - y := by
    simp [NormedSpace.normalize, q, smul_sub, smul_smul, div_eq_mul_inv,
      norm_ne_zero_iff.mpr hy]
  have hdecomp :
      q • x - y = q • (x - y) + (q - 1) • y := by
    module
  have hfirst : ‖q • (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
    nlinarith [norm_nonneg (x - y)]
  have habs : |q - 1| = 1 - q := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq1)]
    ring
  have hsecond : ‖(q - 1) • y‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, habs]
    have hfactor : 0 ≤ 1 - q := sub_nonneg.mpr hq1
    calc
      (1 - q) * ‖y‖ ≤ (1 - q) * ‖x‖ :=
        mul_le_mul_of_nonneg_left hyx hfactor
      _ = ‖x‖ - ‖y‖ := by nlinarith [hqnx]
      _ = |‖x‖ - ‖y‖| := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      _ ≤ ‖x - y‖ := abs_norm_sub_le_norm_sub x y
  calc
    ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
        ‖‖y‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hny]
    _ = ‖q • x - y‖ := by rw [hscaled]
    _ = ‖q • (x - y) + (q - 1) • y‖ := by rw [hdecomp]
    _ ≤ ‖q • (x - y)‖ + ‖(q - 1) • y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add hfirst hsecond
    _ = 2 * ‖x - y‖ := by ring

/-- Homogeneous radial extension of an isometry equivalence between unit spheres.
The origin is treated separately. -/
def radialExtension
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) (x : X) : Y := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖ • (e (normalizeToSphere x hx) : Y)

@[simp] theorem radialExtension_zero
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    radialExtension e 0 = 0 := by
  simp [radialExtension]

theorem radialExtension_of_ne_zero
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    {x : X} (hx : x ≠ 0) :
    radialExtension e x = ‖x‖ • (e (normalizeToSphere x hx) : Y) := by
  simp [radialExtension, hx]

/-- The radial extension preserves the norm of every vector. -/
@[simp] theorem radialExtension_norm
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) (x : X) :
    ‖radialExtension e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [radialExtension_of_ne_zero e hx, norm_smul]
    simp

/-- On the unit sphere, the radial extension agrees with the original map. -/
@[simp] theorem radialExtension_on_sphere
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    (u : Metric.sphere (0 : X) 1) :
    radialExtension e (u : X) = (e u : Y) := by
  rw [radialExtension_of_ne_zero e (ne_zero_of_mem_unit_sphere u)]
  simp

/-- Radial extensions of inverse sphere isometries are left inverses. -/
theorem radialExtension_leftInverse
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    LeftInverse (radialExtension e.symm) (radialExtension e) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hHx : radialExtension e x ≠ 0 := by
      intro hzero
      have : ‖x‖ = 0 := by simpa using congrArg norm hzero
      exact hx (norm_eq_zero.mp this)
    rw [radialExtension_of_ne_zero e.symm hHx]
    have hnorm : ‖radialExtension e x‖ = ‖x‖ := radialExtension_norm e x
    rw [hnorm]
    have hdir :
        normalizeToSphere (radialExtension e x) hHx =
          e (normalizeToSphere x hx) := by
      apply Subtype.ext
      change NormedSpace.normalize (radialExtension e x) =
        (e (normalizeToSphere x hx) : Y)
      rw [radialExtension_of_ne_zero e hx]
      rw [NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr hx)]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (sphere_norm_image e (normalizeToSphere x hx))
    rw [hdir, e.symm_apply_apply]
    exact NormedSpace.norm_smul_normalize x

/-- The opposite composition is proved separately by applying the left-inverse
result to the inverse sphere isometry. -/
theorem radialExtension_rightInverse
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    RightInverse (radialExtension e.symm) (radialExtension e) := by
  exact radialExtension_leftInverse e.symm

private theorem radialExtension_dist_le_three_of_norm_le
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    {x y : X} (hyx : ‖y‖ ≤ ‖x‖) :
    ‖radialExtension e x - radialExtension e y‖ ≤ 3 * ‖x - y‖ := by
  by_cases hy : y = 0
  · subst y
    simp [radialExtension_norm]
    nlinarith [norm_nonneg x]
  have hx : x ≠ 0 := by
    intro hx0
    subst x
    have hy0 : ‖y‖ = 0 := le_antisymm (by simpa using hyx) (norm_nonneg y)
    exact hy (norm_eq_zero.mp hy0)
  let ux : Metric.sphere (0 : X) 1 := normalizeToSphere x hx
  let uy : Metric.sphere (0 : X) 1 := normalizeToSphere y hy
  let ax : Y := (e ux : Y)
  let ay : Y := (e uy : Y)
  have hsplit :
      ‖x‖ • ax - ‖y‖ • ay =
        (‖x‖ • ax - ‖y‖ • ax) + (‖y‖ • ax - ‖y‖ • ay) := by
    module
  have hcoeff : ‖‖x‖ • ax - ‖y‖ • ax‖ = |‖x‖ - ‖y‖| := by
    rw [← sub_smul, norm_smul]
    simp [ax, Real.norm_eq_abs]
  have hang :
      ‖‖y‖ • ax - ‖y‖ • ay‖ =
        ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
    congr 1
    exact sphere_norm_sub_image e ux uy
  rw [radialExtension_of_ne_zero e hx, radialExtension_of_ne_zero e hy]
  change ‖‖x‖ • ax - ‖y‖ • ay‖ ≤ 3 * ‖x - y‖
  rw [hsplit]
  calc
    ‖(‖x‖ • ax - ‖y‖ • ax) + (‖y‖ • ax - ‖y‖ • ay)‖
        ≤ ‖‖x‖ • ax - ‖y‖ • ax‖ + ‖‖y‖ • ax - ‖y‖ • ay‖ :=
          norm_add_le _ _
    _ = |‖x‖ - ‖y‖| +
        ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := by
          rw [hcoeff, hang]
    _ ≤ ‖x - y‖ + 2 * ‖x - y‖ :=
      add_le_add (abs_norm_sub_le_norm_sub x y)
        (scaled_normalize_dist_le_two hx hy hyx)
    _ = 3 * ‖x - y‖ := by ring

private theorem radialExtension_dist_le_three
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) (x y : X) :
    ‖radialExtension e x - radialExtension e y‖ ≤ 3 * ‖x - y‖ := by
  rcases le_total ‖y‖ ‖x‖ with hyx | hxy
  · exact radialExtension_dist_le_three_of_norm_le e hyx
  · have h := radialExtension_dist_le_three_of_norm_le e (x := y) (y := x) hxy
    simpa [norm_sub_rev] using h

/-- The forward radial extension is globally `3`-Lipschitz. -/
theorem lipschitzWith_radialExtension
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    LipschitzWith 3 (radialExtension e) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [dist_eq_norm] using radialExtension_dist_le_three e x y

/-- The radial extension associated with the inverse sphere isometry is also
`3`-Lipschitz. -/
theorem lipschitzWith_radialExtension_symm
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    LipschitzWith 3 (radialExtension e.symm) :=
  lipschitzWith_radialExtension e.symm

/-- The radial extension and the extension of the inverse sphere isometry form
an equivalence of the ambient spaces. -/
noncomputable def radialExtensionEquiv
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) : X ≃ Y where
  toFun := radialExtension e
  invFun := radialExtension e.symm
  left_inv := radialExtension_leftInverse e
  right_inv := radialExtension_rightInverse e

theorem radialExtension_surjective
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    Surjective (radialExtension e) :=
  (radialExtension_rightInverse e).surjective

/-- Norm-preserving homeomorphism obtained from the radial extension.  This is
not asserted to be linear or an ambient isometry. -/
noncomputable def radialExtensionHomeomorph
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) : X ≃ₜ Y where
  toEquiv := radialExtensionEquiv e
  continuous_toFun := (lipschitzWith_radialExtension e).continuous
  continuous_invFun := (lipschitzWith_radialExtension_symm e).continuous

end Sphere
end MathlibAnnex
