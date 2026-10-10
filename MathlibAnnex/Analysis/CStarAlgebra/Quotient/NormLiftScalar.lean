/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# A zero-preserving radial cutoff for norm-minimizing lifts

For `r > 0`, the multiplier correction vanishes on `(-∞, r²]`. The
associated energy equals `min t r²` for nonnegative `t`. Writing the energy
as a polynomial in `t` and the correction avoids using the nonzero constant
function in a nonunital continuous functional calculus.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

/-- A correction, rather than the multiplier itself, so its value at zero is zero. -/
def normLiftCutoff (r t : ℝ) : ℝ := 1 - r / Real.sqrt (max t (r ^ 2))

/-- The squared norm expression produced by the correction. -/
def normLiftEnergy (r t : ℝ) : ℝ :=
  t - t * normLiftCutoff r t - normLiftCutoff r t * t +
    normLiftCutoff r t * t * normLiftCutoff r t

@[fun_prop]
theorem continuous_normLiftCutoff {r : ℝ} (hr : 0 < r) :
    Continuous (normLiftCutoff r) := by
  have hden (t : ℝ) : Real.sqrt (max t (r ^ 2)) ≠ 0 :=
    (Real.sqrt_pos.mpr ((sq_pos_of_pos hr).trans_le (le_max_right t (r ^ 2)))).ne'
  exact continuous_const.sub (continuous_const.div
    (Real.continuous_sqrt.comp (continuous_id.max continuous_const)) hden)

theorem normLiftCutoff_eq_zero_of_le_sq {r t : ℝ} (hr : 0 < r) (ht : t ≤ r ^ 2) :
    normLiftCutoff r t = 0 := by
  simp only [normLiftCutoff, max_eq_right ht, Real.sqrt_sq hr.le,
    div_self hr.ne', sub_self]

@[simp]
theorem normLiftCutoff_zero {r : ℝ} (hr : 0 < r) : normLiftCutoff r 0 = 0 :=
  normLiftCutoff_eq_zero_of_le_sq hr (sq_nonneg r)

@[simp]
theorem normLiftEnergy_zero (r : ℝ) : normLiftEnergy r 0 = 0 := by
  simp [normLiftEnergy]

theorem normLiftEnergy_eq_min {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    normLiftEnergy r t = min t (r ^ 2) := by
  have hpoly : normLiftEnergy r t = t * (1 - normLiftCutoff r t) ^ 2 := by
    unfold normLiftEnergy
    ring
  by_cases hle : t ≤ r ^ 2
  · rw [hpoly, normLiftCutoff_eq_zero_of_le_sq hr hle, min_eq_left hle]
    ring
  · have hgt : r ^ 2 < t := lt_of_not_ge hle
    have htpos : 0 < t := (sq_nonneg r).trans_lt hgt
    rw [hpoly, min_eq_right hgt.le]
    have hsub : 1 - normLiftCutoff r t = r / Real.sqrt t := by
      simp only [normLiftCutoff, max_eq_left hgt.le]
      ring
    rw [hsub, div_pow, Real.sq_sqrt ht]
    field_simp [htpos.ne'] <;> ring

/-- This is the scalar estimate used in the original algebra's C-star norm. -/
theorem norm_normLiftEnergy_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    ‖normLiftEnergy r t‖ ≤ r ^ 2 := by
  rw [normLiftEnergy_eq_min hr ht, Real.norm_eq_abs,
    abs_of_nonneg (le_min ht (sq_nonneg r))]
  exact min_le_right _ _

end MathlibAnnex.Analysis.CStarAlgebra
