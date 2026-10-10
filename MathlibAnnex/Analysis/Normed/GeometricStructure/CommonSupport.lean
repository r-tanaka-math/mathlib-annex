/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Support
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.RCLike.Extend

public import Mathlib.Tactic.Linarith

/-!
# Common supporting functionals on convex subsets of the unit sphere

The real proof separates the open ball from the whole convex set, not one point
at a time. The separating constant is strictly positive since zero is in the
open ball. The polar-ball identity gives the norm bound after normalization.
The RCLike extension preserves the norm and the real part; equality in the
scalar unit ball then recovers the complex value one.

No completeness, finite dimension, separability, or uniqueness is assumed.
The compatible real scalar structure can always be the canonical restriction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

/-- A nonempty real-convex subset of the unit sphere has a common real support. -/
theorem exists_dual_eq_one_of_convex_subset_sphere_real
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hsphere : C ⊆ sphere (0 : E) 1) :
    ∃ f : StrongDual ℝ E, ‖f‖ = 1 ∧ ∀ x ∈ C, f x = 1 := by
  have hdisj : Disjoint (ball (0 : E) 1) C := by
    refine Set.disjoint_left.2 ?_
    intro x hx hxc
    have hxlt : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
    have hxeq : ‖x‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hsphere hxc
    exact (ne_of_lt hxlt) hxeq
  obtain ⟨f, r, hball, hC⟩ :=
    geometric_hahn_banach_open (convex_ball (0 : E) 1) isOpen_ball hconv hdisj
  have hr : 0 < r := by
    simpa only [map_zero] using hball 0 (mem_ball_self zero_lt_one)
  let g : StrongDual ℝ E := r⁻¹ • f
  have hgpolar : g ∈ StrongDual.polar ℝ (ball (0 : E) 1) := by
    change ∀ x ∈ ball (0 : E) 1, ‖g x‖ ≤ 1
    intro x hx
    have hxneg : -x ∈ ball (0 : E) 1 := by
      simpa only [mem_ball_zero_iff, norm_neg] using hx
    have hfupper : f x ≤ r := (hball x hx).le
    have hflower : -r ≤ f x := by
      have h := hball (-x) hxneg
      rw [map_neg] at h
      linarith
    have hfnorm : ‖f x‖ ≤ r := by
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨hflower, hfupper⟩
    change ‖r⁻¹ • f x‖ ≤ 1
    calc
      ‖r⁻¹ • f x‖ = r⁻¹ * ‖f x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hfnorm (inv_nonneg.2 hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hgnorm : ‖g‖ ≤ 1 := by
    rw [NormedSpace.polar_ball (𝕜 := ℝ) (E := E) zero_lt_one] at hgpolar
    simpa only [inv_one, mem_closedBall_zero_iff] using hgpolar
  have hgC : ∀ x ∈ C, g x = 1 := by
    intro x hx
    have hxeq : ‖x‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hsphere hx
    have hlower : 1 ≤ g x := by
      change 1 ≤ r⁻¹ * f x
      calc
        1 = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
        _ ≤ r⁻¹ * f x := mul_le_mul_of_nonneg_left (hC x hx) (inv_nonneg.2 hr.le)
    have hupper : g x ≤ 1 := calc
      g x ≤ ‖g x‖ := le_abs_self _
      _ ≤ ‖g‖ * ‖x‖ := g.le_opNorm x
      _ ≤ 1 := by simpa only [hxeq, mul_one] using hgnorm
    exact le_antisymm hupper hlower
  refine ⟨g, ?_, hgC⟩
  exact norm_eq_one_of_mem_supportFunctionals ℝ hne
    (fun x hx => (show ‖x‖ = 1 by
      simpa only [mem_sphere, dist_zero_right] using hsphere hx).le) ⟨hgnorm, hgC⟩

/-- The common-support theorem over a real or complex scalar field, using a
compatible real restriction. Nonemptiness is indispensable in the zero space. -/
theorem exists_dual_eq_one_of_convex_subset_sphere
    (𝕜 : Type v) [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {C : Set E} (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hsphere : C ⊆ sphere (0 : E) 1) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧ ∀ x ∈ C, f x = 1 := by
  obtain ⟨g, hgnorm, hgC⟩ :=
    exists_dual_eq_one_of_convex_subset_sphere_real hne hconv hsphere
  let f : StrongDual 𝕜 E := g.extendRCLike
  have hfnorm : ‖f‖ = 1 := (StrongDual.norm_extendRCLike g).trans hgnorm
  refine ⟨f, hfnorm, ?_⟩
  intro x hx
  have hre : RCLike.re (f x) = 1 := by
    simpa only [f, StrongDual.re_extendRCLike_apply] using hgC x hx
  have hn : ‖f x‖ ≤ 1 := by
    have hxnorm : ‖x‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hsphere hx
    simpa only [hfnorm, hxnorm, one_mul] using f.le_opNorm x
  have h := RCLike.re_eq_self_of_le (a := f x) (hn.trans hre.ge)
  simpa only [hre, algebraMap.coe_one] using h.symm

/-- The existing support-family carrier is nonempty for a nonempty convex
sphere subset. This does not say that the support is unique. -/
theorem nonempty_supportFunctionals_of_convex_subset_sphere
    (𝕜 : Type v) [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {C : Set E} (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hsphere : C ⊆ sphere (0 : E) 1) :
    (supportFunctionals 𝕜 C).Nonempty := by
  obtain ⟨f, hf, hC⟩ := exists_dual_eq_one_of_convex_subset_sphere 𝕜 hne hconv hsphere
  exact ⟨f, hf.le, hC⟩

end NormedSpace
