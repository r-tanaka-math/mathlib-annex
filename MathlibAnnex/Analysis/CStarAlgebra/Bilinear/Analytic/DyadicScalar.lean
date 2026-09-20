import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-!
# Finite continuous dyadic slices

The functions are continuous real functions.  The telescoping identity is
finite and exact, and the fourth-power majorant has no dimension-dependent
constant.  No measurable spectral projections or integrals are used.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace MathlibAnnex.CStarBilinear.Analytic

/-- Soft truncation of the positive part at a positive level. -/
def truncatePos (L x : ℝ) : ℝ := min (max x 0) L

/-- Initial effect at the cutoff `T`. -/
def baseSlice (T x : ℝ) : ℝ := truncatePos T x / T

/-- The slice between two successive dyadic levels. -/
def softSlice (L x : ℝ) : ℝ :=
  (truncatePos (2 * L) x - truncatePos L x) / L

/-- The `n`th dyadic level. -/
def dyadicLevel (T : ℝ) (n : ℕ) : ℝ := 2 ^ n * T

@[simp] theorem dyadicLevel_zero (T : ℝ) : dyadicLevel T 0 = T := by
  simp [dyadicLevel]

theorem dyadicLevel_succ (T : ℝ) (n : ℕ) :
    dyadicLevel T (n + 1) = 2 * dyadicLevel T n := by
  simp [dyadicLevel, pow_succ]
  ring

theorem dyadicLevel_pos {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < dyadicLevel T n := by unfold dyadicLevel; positivity

theorem continuous_truncatePos (L : ℝ) : Continuous (truncatePos L) := by
  unfold truncatePos
  fun_prop

theorem continuous_baseSlice (T : ℝ) : Continuous (baseSlice T) := by
  unfold baseSlice truncatePos
  fun_prop

theorem continuous_softSlice (L : ℝ) : Continuous (softSlice L) := by
  unfold softSlice truncatePos
  fun_prop

theorem baseSlice_nonneg {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ baseSlice T x :=
  div_nonneg (le_min (le_max_right _ _) hT.le) hT.le

theorem baseSlice_le_one {T : ℝ} (hT : 0 < T) (x : ℝ) :
    baseSlice T x ≤ 1 := by
  apply (div_le_iff₀ hT).mpr
  simpa [truncatePos] using (min_le_right (max x 0) T)

theorem softSlice_nonneg {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 ≤ softSlice L x := by
  apply div_nonneg _ hL.le
  apply sub_nonneg.mpr
  exact min_le_min_left _ (by linarith)

theorem softSlice_le_one {L : ℝ} (hL : 0 < L) (x : ℝ) :
    softSlice L x ≤ 1 := by
  apply (div_le_iff₀ hL).mpr
  by_cases hx : max x 0 ≤ L
  · have hx2 : max x 0 ≤ 2 * L := by linarith
    simp only [truncatePos, min_eq_left hx, min_eq_left hx2]
    linarith
  · have hLx : L ≤ max x 0 := le_of_lt (lt_of_not_ge hx)
    rw [truncatePos, truncatePos, min_eq_right hLx]
    have hmin := min_le_right (max x 0) (2 * L)
    linarith

theorem softSlice_eq_zero_of_le {L x : ℝ} (hL : 0 < L) (hx : x ≤ L) :
    softSlice L x = 0 := by
  have hm : max x 0 ≤ L := max_le hx hL.le
  have hm2 : max x 0 ≤ 2 * L := by linarith
  simp [softSlice, truncatePos, min_eq_left hm, min_eq_left hm2]

/-- Every tail effect is bounded by the same fourth-power function at its
own scale.  This simple support bound avoids a measure-theoretic tail lemma. -/
theorem softSlice_le_fourth {L : ℝ} (hL : 0 < L) (x : ℝ) :
    softSlice L x ≤ x ^ 4 / L ^ 4 := by
  by_cases hx : x ≤ L
  · rw [softSlice_eq_zero_of_le hL hx]
    positivity
  · have hLx : L ≤ x := le_of_lt (lt_of_not_ge hx)
    have hpow : L ^ 4 ≤ x ^ 4 := by gcongr
    have hdiv : 1 ≤ x ^ 4 / L ^ 4 := by
      apply (le_div_iff₀ (pow_pos hL 4)).mpr
      simpa using hpow
    exact (softSlice_le_one hL x).trans hdiv

theorem level_mul_softSlice {L : ℝ} (hL : 0 < L) (x : ℝ) :
    L * softSlice L x = truncatePos (2 * L) x - truncatePos L x := by
  unfold softSlice
  field_simp [ne_of_gt hL]

/-- Finite telescoping before a terminal cutoff is chosen. -/
theorem dyadic_telescope {T : ℝ} (hT : 0 < T) (N : ℕ) (x : ℝ) :
    truncatePos T x + ∑ k ∈ range N,
      dyadicLevel T k * softSlice (dyadicLevel T k) x =
        truncatePos (dyadicLevel T N) x := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ]
      rw [← add_assoc, ih, level_mul_softSlice (dyadicLevel_pos hT N),
        dyadicLevel_succ]
      ring

/-- Positive minus negative truncation is exactly the original scalar once
the terminal cutoff dominates its absolute value. -/
theorem signed_truncate_eq {L x : ℝ} (hx : |x| ≤ L) :
    truncatePos L x - truncatePos L (-x) = x := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hx
  have hpos : max x 0 ≤ L := max_le ((le_abs_self _).trans hx) hL
  have hneg : max (-x) 0 ≤ L := max_le ((neg_le_abs _).trans hx) hL
  simp only [truncatePos, min_eq_left hpos, min_eq_left hneg]
  by_cases h : 0 ≤ x
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hx0 : x ≤ 0 := le_of_not_ge h
    rw [max_eq_right hx0, max_eq_left (neg_nonneg.mpr hx0)]
    ring

/-- An exact signed continuous finite-slice expansion. -/
theorem signed_dyadic_telescope {T : ℝ} (hT : 0 < T) (N : ℕ) (x : ℝ)
    (hx : |x| ≤ dyadicLevel T N) :
    truncatePos T x + ∑ k ∈ range N,
        dyadicLevel T k * softSlice (dyadicLevel T k) x -
      (truncatePos T (-x) + ∑ k ∈ range N,
        dyadicLevel T k * softSlice (dyadicLevel T k) (-x)) = x := by
  rw [dyadic_telescope hT, dyadic_telescope hT]
  exact signed_truncate_eq hx

/-- Exact finite geometric identity. -/
theorem dyadic_reciprocal_sum (N : ℕ) :
    ∑ k ∈ range N, (1 : ℝ) / 2 ^ k = 2 - 2 / 2 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [sum_range_succ, ih, pow_succ]
      field_simp <;> ring

theorem dyadic_reciprocal_sum_le (N : ℕ) :
    ∑ k ∈ range N, (1 : ℝ) / 2 ^ k ≤ 2 := by
  rw [dyadic_reciprocal_sum]
  have h : (0 : ℝ) ≤ 2 / 2 ^ N := by positivity
  linarith

/-- Square-root tail cost at one scale.  The zero-moment case is included. -/
theorem weighted_sqrt_le_of_fourth_bound {L u m : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hm : 0 ≤ m) (hub : u ≤ m / L ^ 4) :
    L * Real.sqrt u ≤ Real.sqrt m / L := by
  have hbound : u * L ^ 4 ≤ m := (le_div_iff₀ (pow_pos hL 4)).mp hub
  have hsquares : (L ^ 2 * Real.sqrt u) ^ 2 ≤ (Real.sqrt m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hm]
    nlinarith [hbound]
  have hroot : L ^ 2 * Real.sqrt u ≤ Real.sqrt m := by
    nlinarith [Real.sqrt_nonneg m, mul_nonneg (sq_nonneg L) (Real.sqrt_nonneg u)]
  apply (le_div_iff₀ hL).mpr
  nlinarith [hroot]

end MathlibAnnex.CStarBilinear.Analytic
