/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.PreorderFilter
public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFace

/-!
# Convex sphere sets and norm-attainment filters

A common norming functional at an interior segment point norms both endpoints.
Consequently real-convex sphere sets are downward directed in the orthogonality
preorder. A contractive functional's absolute norm-attainment set is an order
filter. This supplies actual filters, not a structure assuming their existence.
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

/-- A functional norming a sphere point in an open segment also norms its
endpoints, when they lie on the sphere. -/
theorem normingFunctionals_subset_of_mem_openSegment {x y z : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) (hseg : z ∈ openSegment ℝ x y) :
    normingFunctionals 𝕜 z ⊆ normingFunctionals 𝕜 x ∩ normingFunctionals 𝕜 y := by
  intro f hf
  have hface := isExtreme_unitBallSupportFace 𝕜 hf.1
  have hzface : z ∈ unitBallSupportFace 𝕜 f :=
    ⟨mem_closedBall_zero_iff.mpr hz.le,
      by simpa only [Set.mem_setOf_eq, hz, algebraMap.coe_one] using hf.2⟩
  have hxball : x ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.mpr hx.le
  have hyball : y ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.mpr hy.le
  have hxface := hface.2 hxball hyball hzface hseg
  have hyface := hface.2 hyball hxball hzface (by rwa [openSegment_symm])
  exact ⟨⟨hf.1, by simpa only [Set.mem_setOf_eq, hx, algebraMap.coe_one] using hxface.2⟩,
    ⟨hf.1, by simpa only [Set.mem_setOf_eq, hy, algebraMap.coe_one] using hyface.2⟩⟩

theorem birkhoffJamesOrthogonalSet_subset_of_mem_openSegment {x y z : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) (hseg : z ∈ openSegment ℝ x y) :
    birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∩
      birkhoffJamesOrthogonalSet 𝕜 y := by
  intro w hw
  obtain ⟨f, hf, hfw⟩ :=
    BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero 𝕜 hw
  have hfxy := normingFunctionals_subset_of_mem_openSegment 𝕜 hx hy hz hseg hf
  exact ⟨birkhoffJamesOrthogonal_of_mem_normingFunctionals_apply_eq_zero 𝕜 hfxy.1 hfw,
    birkhoffJamesOrthogonal_of_mem_normingFunctionals_apply_eq_zero 𝕜 hfxy.2 hfw⟩

/-- Convex sphere sets are downward directed for inclusion of their right
orthogonality sets. The midpoint is an actual lower bound. -/
theorem directed_birkhoffJamesOrthogonalSet_of_convex_subset_sphere {C : Set E}
    (hconv : Convex ℝ C) (hsphere : C ⊆ sphere (0 : E) 1) :
    ∀ x ∈ C, ∀ y ∈ C, ∃ z ∈ C,
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y := by
  intro x hx y hy
  let z : E := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hz : z ∈ C := hconv hx hy (by norm_num) (by norm_num) (by norm_num)
  have hsub := birkhoffJamesOrthogonalSet_subset_of_mem_openSegment 𝕜
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hx)
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hy)
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hz)
    (show z ∈ openSegment ℝ x y from ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩)
  exact ⟨z, hz, fun _ h => (hsub h).1, fun _ h => (hsub h).2⟩

/-- Absolute norm attainment can be rotated and normalized to the existing
value-one support face. -/
theorem inv_apply_smul_mem_unitBallSupportFace {f : StrongDual 𝕜 E} {x : E}
    (hf : f ∈ absoluteNormingFunctionals 𝕜 x) (hx : x ≠ 0) :
    (f x)⁻¹ • x ∈ unitBallSupportFace 𝕜 f := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hfx : f x ≠ 0 := norm_ne_zero_iff.mp (hf.2.trans_ne hxnorm)
  refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · rw [norm_smul, norm_inv, hf.2, inv_mul_cancel₀ hxnorm]
  · change f ((f x)⁻¹ • x) = 1
    rw [f.map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hfx

/-- A scalar equality case used to make the phase on a convex sphere set
constant. This is not a uniqueness claim for supporting functionals. -/
private theorem eq_one_of_norm_add_one {z : 𝕜} (hz : ‖z‖ ≤ 1) (hadd : ‖z + 1‖ = 2) :
    z = 1 := by
  have hsq := RCLike.norm_sq_eq_def (z := z + 1)
  have hsqz := RCLike.norm_sq_eq_def (z := z)
  simp only [hadd, map_add, RCLike.one_re, RCLike.one_im, add_zero] at hsq
  have hnormsq : ‖z‖ ^ 2 ≤ 1 := by
    simpa only [pow_two, mul_one] using mul_le_mul hz hz (norm_nonneg z) zero_le_one
  have hre : RCLike.re z = 1 := by
    have hr := RCLike.re_le_norm z
    have hn := norm_nonneg z
    nlinarith [hsq, hsqz, hnormsq]
  have heq := RCLike.re_eq_self_of_le (a := z) (hz.trans hre.ge)
  simpa only [hre, algebraMap.coe_one] using heq.symm

/-- Absolute norm-one values on a convex sphere set have a constant phase.
Here that phase has already been normalized at one member of the set. -/
theorem eq_one_on_convex_of_norm_apply_eq_one {C : Set E} (hconv : Convex ℝ C)
    {f : StrongDual 𝕜 E} (habs : ∀ x ∈ C, ‖f x‖ = 1) {x₀ : E}
    (hx₀ : x₀ ∈ C) (hfx₀ : f x₀ = 1) : ∀ x ∈ C, f x = 1 := by
  intro x hx
  let z : E := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x₀
  have hz : z ∈ C := hconv hx hx₀ (by norm_num) (by norm_num) (by norm_num)
  have hmap : f z = (1 / 2 : ℝ) • (f x + 1) := by
    change (f.restrictScalars ℝ) ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x₀) = _
    rw [map_add, map_smul, map_smul]
    change (1 / 2 : ℝ) • f x + (1 / 2 : ℝ) • f x₀ = (1 / 2 : ℝ) • (f x + 1)
    rw [hfx₀, smul_add]
  have hnorm : ‖f x + 1‖ = 2 := by
    have h := habs z hz
    rw [hmap, norm_smul] at h
    norm_num at h
    linarith
  exact eq_one_of_norm_add_one 𝕜 (habs x hx).le hnorm

/-- A common absolute support on a nonempty convex sphere set can be multiplied
by one unit scalar to become a common value-one support on the entire set. -/
theorem exists_norm_eq_one_smul_mem_supportFunctionals {C : Set E} (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hsphere : C ⊆ sphere (0 : E) 1)
    {f : StrongDual 𝕜 E} (hf : ∀ x ∈ C, f ∈ absoluteNormingFunctionals 𝕜 x) :
    ∃ a : 𝕜, ‖a‖ = 1 ∧ a • f ∈ supportFunctionals 𝕜 C := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hfx₀norm : ‖f x₀‖ = 1 := (hf x₀ hx₀).2.trans
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hx₀)
  have hfx₀ : f x₀ ≠ 0 := norm_ne_zero_iff.mp (hfx₀norm.trans_ne one_ne_zero)
  let a : 𝕜 := (f x₀)⁻¹
  let g : StrongDual 𝕜 E := a • f
  have ha : ‖a‖ = 1 := by simp only [a, norm_inv, hfx₀norm, inv_one]
  have hg : ‖g‖ ≤ 1 := by
    simpa only [g, norm_smul, ha, one_mul] using (hf x₀ hx₀).1
  have habs : ∀ x ∈ C, ‖g x‖ = 1 := by
    intro x hx
    change ‖a * f x‖ = 1
    rw [norm_mul, ha, one_mul, (hf x hx).2]
    simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hx
  have hgx₀ : g x₀ = 1 := inv_mul_cancel₀ hfx₀
  exact ⟨a, ha, hg, eq_one_on_convex_of_norm_apply_eq_one 𝕜 hconv habs hx₀ hgx₀⟩

/-- The set of vectors where a fixed functional attains the norm in absolute
value. This is a subset of `E`, not a second family of functionals. -/
def absoluteNormAttainmentSet (f : StrongDual 𝕜 E) : Set E :=
  {x | ‖f x‖ = ‖x‖}

/-- The absolute norm-attainment set of a contractive functional is a genuine
preorder filter. Nonattaining functionals are allowed. -/
theorem isBirkhoffJamesFilter_absoluteNormAttainmentSet {f : StrongDual 𝕜 E}
    (hf : ‖f‖ ≤ 1) : IsBirkhoffJamesFilter 𝕜 (absoluteNormAttainmentSet 𝕜 f) := by
  apply (isBirkhoffJamesFilter_iff 𝕜 _).mpr
  refine ⟨⟨0, by simp [absoluteNormAttainmentSet]⟩, ?_, ?_⟩
  · intro x hx y hy
    by_cases hx₀ : x = 0
    · refine ⟨y, hy, ?_, Subset.rfl⟩
      rw [hx₀, birkhoffJamesOrthogonalSet_zero]
      exact subset_univ _
    by_cases hy₀ : y = 0
    · refine ⟨x, hx, Subset.rfl, ?_⟩
      rw [hy₀, birkhoffJamesOrthogonalSet_zero]
      exact subset_univ _
    let u := (f x)⁻¹ • x
    let v := (f y)⁻¹ • y
    have hu : u ∈ unitBallSupportFace 𝕜 f := inv_apply_smul_mem_unitBallSupportFace 𝕜 ⟨hf, hx⟩ hx₀
    have hv : v ∈ unitBallSupportFace 𝕜 f := inv_apply_smul_mem_unitBallSupportFace 𝕜 ⟨hf, hy⟩ hy₀
    obtain ⟨z, hz, hzu, hzv⟩ := directed_birkhoffJamesOrthogonalSet_of_convex_subset_sphere 𝕜
      (convex_unitBallSupportFace 𝕜 f) (unitBallSupportFace_subset_sphere 𝕜 hf) u hu v hv
    have hfx : f x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne (norm_ne_zero_iff.mpr hx₀))
    have hfy : f y ≠ 0 := norm_ne_zero_iff.mp (hy.trans_ne (norm_ne_zero_iff.mpr hy₀))
    refine ⟨z, ?_, ?_, ?_⟩
    · change ‖f z‖ = ‖z‖
      have hfz : f z = 1 := hz.2
      rw [hfz, norm_one]
      symm
      simpa only [Metric.mem_sphere, dist_zero_right] using
        unitBallSupportFace_subset_sphere 𝕜 hf hz
    · change birkhoffJamesOrthogonalSet 𝕜 z ⊆
        birkhoffJamesOrthogonalSet 𝕜 ((f x)⁻¹ • x) at hzu
      rwa [birkhoffJamesOrthogonalSet_smul 𝕜 (inv_ne_zero hfx)] at hzu
    · change birkhoffJamesOrthogonalSet 𝕜 z ⊆
        birkhoffJamesOrthogonalSet 𝕜 ((f y)⁻¹ • y) at hzv
      rwa [birkhoffJamesOrthogonalSet_smul 𝕜 (inv_ne_zero hfy)] at hzv
  · intro x y hxy hx
    exact ((birkhoffJamesOrthogonalSet_subset_iff 𝕜).mp hxy ⟨hf, hx⟩).2

end NormedSpace
