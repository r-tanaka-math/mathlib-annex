/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

/-! # Isometric l1 pairs and extreme points

These generic normed-space statements are independent of C*-algebras.
The two proof bodies were moved unchanged from the R8 coefficient-pair module.
-/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace NormedSpace

/-- An isometric l1 pair is linearly independent, with both zero coefficients
accounted for. No strict convexity of the surrounding space is required. -/
theorem smul_add_eq_zero_iff_of_norm_smul_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V) (hl1 : ∀ a b : ℂ, ‖a • f + b • g‖ = ‖a‖ + ‖b‖)
    (a b : ℂ) : a • f + b • g = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hn := hl1 a b
    rw [h, norm_zero] at hn
    exact ⟨norm_eq_zero.mp (by linarith [norm_nonneg a, norm_nonneg b]),
      norm_eq_zero.mp (by linarith [norm_nonneg a, norm_nonneg b])⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- An extreme unit vector in the span of an isometric l1 pair lies on one
coordinate line. The convex decomposition is exhibited with positive real
weights; no extremality of the linear extension or of an image is assumed. -/
theorem eq_zero_or_eq_zero_of_extreme_smul_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (hl1 : ∀ a b : ℂ, ‖a • f + b • g‖ = ‖a‖ + ‖b‖)
    (a b : ℂ) (hext : a • f + b • g ∈ (closedBall (0 : V) 1).extremePoints ℝ)
    (hn : ‖a • f + b • g‖ = 1) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr hb
  exfalso
  let s : ℝ := ‖a‖
  let t : ℝ := ‖b‖
  have hs : 0 < s := norm_pos_iff.mpr ha
  have ht : 0 < t := norm_pos_iff.mpr hb
  have hst : s + t = 1 := (hl1 a b).symm.trans hn
  let u : V := s⁻¹ • (a • f)
  let v : V := t⁻¹ • (b • g)
  have hu : u ∈ closedBall (0 : V) 1 := by
    apply mem_closedBall_zero_iff.mpr
    calc
      ‖u‖ = s⁻¹ * (‖a‖ * ‖f‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
      _ = 1 := by rw [hf, mul_one]; exact inv_mul_cancel₀ hs.ne'
      _ ≤ 1 := le_rfl
  have hv : v ∈ closedBall (0 : V) 1 := by
    apply mem_closedBall_zero_iff.mpr
    calc
      ‖v‖ = t⁻¹ * (‖b‖ * ‖g‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      _ = 1 := by rw [hg, mul_one]; exact inv_mul_cancel₀ ht.ne'
      _ ≤ 1 := le_rfl
  have hcomb : s • u + t • v = a • f + b • g := by
    simp only [u, v, smul_smul, mul_inv_cancel₀ hs.ne', mul_inv_cancel₀ ht.ne', one_smul]
  have heq : u = a • f + b • g := hext.2 hu hv ⟨s, t, hs, ht, hst, hcomb⟩
  have heq' : (((s⁻¹ : ℝ) : ℂ) * a) • f = a • f + b • g := by
    change ((s⁻¹ : ℝ) : ℂ) • (a • f) = a • f + b • g at heq
    simpa only [smul_smul] using heq
  have hz : (a - ((s⁻¹ : ℝ) : ℂ) * a) • f + b • g = 0 := by
    rw [sub_smul]
    calc
      a • f - (((s⁻¹ : ℝ) : ℂ) * a) • f + b • g =
          (a • f + b • g) - ((((s⁻¹ : ℝ) : ℂ) * a) • f) := by abel
      _ = 0 := sub_eq_zero.mpr heq'.symm
  exact hb ((smul_add_eq_zero_iff_of_norm_smul_add f g hl1 _ _).1 hz).2

end NormedSpace
