/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Birkhoff-James orthogonality

The relation uses all scalars of the stated field. Its elementary properties
hold in seminormed spaces over any normed field, without completeness.
The dual-functional characterization is proved in `JamesWitness`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [NormedField 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Adding any scalar multiple of the second vector cannot decrease the norm
of the first vector. -/
def BirkhoffJamesOrthogonal (x y : E) : Prop :=
  ∀ a : 𝕜, ‖x‖ ≤ ‖x + a • y‖

variable {𝕜}

/-- A vector with zero seminorm is orthogonal to every vector. -/
theorem birkhoffJamesOrthogonal_of_norm_eq_zero {x y : E} (hx : ‖x‖ = 0) :
    BirkhoffJamesOrthogonal 𝕜 x y := by
  intro a
  rw [hx]
  exact norm_nonneg _

@[simp]
theorem birkhoffJamesOrthogonal_zero_left (y : E) :
    BirkhoffJamesOrthogonal 𝕜 0 y :=
  birkhoffJamesOrthogonal_of_norm_eq_zero (norm_zero : ‖(0 : E)‖ = 0)

@[simp]
theorem birkhoffJamesOrthogonal_zero_right (x : E) :
    BirkhoffJamesOrthogonal 𝕜 x 0 := by
  intro a
  simp

/-- The self-orthogonality test in a seminormed space. -/
theorem birkhoffJamesOrthogonal_self_iff_norm_eq_zero (x : E) :
    BirkhoffJamesOrthogonal 𝕜 x x ↔ ‖x‖ = 0 := by
  constructor
  · intro h
    have h' := h (-1)
    have hx : ‖x‖ ≤ 0 := by simpa using h'
    exact le_antisymm hx (norm_nonneg x)
  · exact birkhoffJamesOrthogonal_of_norm_eq_zero

/-- A homogeneous form of the defining inequality. The zero coefficient is
handled separately, so no linear independence or nonzero-vector assumption
is needed. -/
theorem BirkhoffJamesOrthogonal.norm_mul_le {x y : E}
    (h : BirkhoffJamesOrthogonal 𝕜 x y) (a b : 𝕜) :
    ‖a‖ * ‖x‖ ≤ ‖a • x + b • y‖ := by
  by_cases ha : a = 0
  · subst a
    simp only [norm_zero, zero_mul, zero_smul, zero_add]
    exact norm_nonneg _
  · have hb : a * (a⁻¹ * b) = b := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    calc
      ‖a‖ * ‖x‖ ≤ ‖a‖ * ‖x + (a⁻¹ * b) • y‖ :=
        mul_le_mul_of_nonneg_left (h _) (norm_nonneg a)
      _ = ‖a • (x + (a⁻¹ * b) • y)‖ := (norm_smul _ _).symm
      _ = ‖a • x + b • y‖ := by rw [smul_add, smul_smul, hb]

/-- Birkhoff-James orthogonality is homogeneous in both variables, including
zero scalars. -/
theorem BirkhoffJamesOrthogonal.smul {x y : E}
    (h : BirkhoffJamesOrthogonal 𝕜 x y) (a b : 𝕜) :
    BirkhoffJamesOrthogonal 𝕜 (a • x) (b • y) := by
  intro c
  rw [norm_smul, smul_smul]
  exact h.norm_mul_le a (c * b)

theorem birkhoffJamesOrthogonal_smul_iff {x y : E} {a b : 𝕜}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    BirkhoffJamesOrthogonal 𝕜 (a • x) (b • y) ↔
      BirkhoffJamesOrthogonal 𝕜 x y := by
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, one_smul]
      using h.smul a⁻¹ b⁻¹
  · intro h
    exact h.smul a b

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

@[simp]
theorem birkhoffJamesOrthogonal_self_iff (x : V) :
    BirkhoffJamesOrthogonal 𝕜 x x ↔ x = 0 := by
  rw [birkhoffJamesOrthogonal_self_iff_norm_eq_zero, norm_eq_zero]

end Normed

end NormedSpace
