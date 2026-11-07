/- R6 dyadic interpolation, actual band formulas and endpoint agreement.
These local band results are assembled into the global clock in ScaleClock.Global
and the direction/energy constructions in ScaleClock and Coding.
Local execution evidence is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.TailProjections
import BanachGeometry.HilbertSums.Coding.UnitSegment
import Mathlib.Analysis.PSeries

noncomputable section
open scoped BigOperators Topology
open Filter
namespace BanachGeometry.HilbertSums

def dyadicRadius (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m
def dyadicSlope (c : ℝ) (m : ℕ) : ℝ := c * (2 : ℝ) ^ m / (8 * (m + 1))
def harmonicClockEndpoint (c : ℝ) (m : ℕ) : ℝ :=
  (c / 16) * ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 1)
def clockOnBand (c : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  harmonicClockEndpoint c m + dyadicSlope c m * (dyadicRadius m - r)

theorem dyadicRadius_pos (m : ℕ) : 0 < dyadicRadius m := by
  unfold dyadicRadius
  positivity

theorem dyadicRadius_succ (m : ℕ) : dyadicRadius (m + 1) = dyadicRadius m / 2 := by
  unfold dyadicRadius
  rw [pow_succ]
  ring

theorem dyadicRadius_mul_pow (m : ℕ) : dyadicRadius m * (2 : ℝ) ^ m = 1 := by
  unfold dyadicRadius
  rw [← mul_pow]
  norm_num

theorem tendsto_dyadicRadius_zero : Tendsto dyadicRadius atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem dyadicSlope_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 ≤ dyadicSlope c m := by
  unfold dyadicSlope
  positivity

theorem dyadicSlope_pos {c : ℝ} (hc : 0 < c) (m : ℕ) : 0 < dyadicSlope c m := by
  unfold dyadicSlope
  positivity

theorem dyadicSlope_mul_radius (c : ℝ) (m : ℕ) :
    dyadicSlope c m * dyadicRadius m = c / (8 * (m + 1)) := by
  unfold dyadicSlope
  calc
    (c * 2 ^ m / (8 * (m + 1))) * dyadicRadius m =
        c * (dyadicRadius m * 2 ^ m) / (8 * (m + 1)) := by ring
    _ = _ := by rw [dyadicRadius_mul_pow, mul_one]

theorem dyadic_band_increment (c : ℝ) (m : ℕ) :
    dyadicSlope c m * (dyadicRadius m - dyadicRadius (m + 1)) =
      c / (16 * (m + 1)) := by
  rw [dyadicRadius_succ]
  calc
    dyadicSlope c m * (dyadicRadius m - dyadicRadius m / 2) =
        (dyadicSlope c m * dyadicRadius m) / 2 := by ring
    _ = c / (8 * (m + 1)) / 2 := by rw [dyadicSlope_mul_radius]
    _ = _ := by
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hm]
      ring

theorem harmonicClockEndpoint_succ (c : ℝ) (m : ℕ) :
    harmonicClockEndpoint c (m + 1) = harmonicClockEndpoint c m + c / (16 * (m + 1)) := by
  simp only [harmonicClockEndpoint, Finset.sum_range_succ]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm]

theorem tendsto_harmonicClockEndpoint_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (harmonicClockEndpoint c) atTop atTop := by
  change Tendsto (fun m => (c / 16) * ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 1)) atTop atTop
  exact
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
      (div_pos hc (by norm_num : (0 : ℝ) < 16))

theorem clockOnBand_upper_endpoint (c : ℝ) (m : ℕ) :
    clockOnBand c m (dyadicRadius m) = harmonicClockEndpoint c m := by
  simp [clockOnBand]

/-- Adjacent affine pieces agree at their common dyadic endpoint. -/
theorem clockOnBand_lower_endpoint (c : ℝ) (m : ℕ) :
    clockOnBand c m (dyadicRadius (m + 1)) = harmonicClockEndpoint c (m + 1) := by
  rw [clockOnBand, dyadic_band_increment, harmonicClockEndpoint_succ]

theorem clockOnBand_abs_sub {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (r s : ℝ) :
    |clockOnBand c m r - clockOnBand c m s| = dyadicSlope c m * |r - s| := by
  have hid : clockOnBand c m r - clockOnBand c m s = -(dyadicSlope c m * (r - s)) := by
    unfold clockOnBand
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg (dyadicSlope_nonneg hc m)]

/-- The exact c²/64 weight multiplying the reciprocal-square series in R6. -/
theorem dyadic_weight_identity (c : ℝ) (m : ℕ) :
    dyadicRadius m ^ 2 * dyadicSlope c m ^ 2 =
      (c ^ 2 / 64) * (1 / ((m : ℝ) + 1) ^ 2) := by
  calc
    dyadicRadius m ^ 2 * dyadicSlope c m ^ 2 = (dyadicSlope c m * dyadicRadius m) ^ 2 := by ring
    _ = (c / (8 * (m + 1))) ^ 2 := by rw [dyadicSlope_mul_radius]
    _ = _ := by
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hm]
      ring

theorem summable_one_div_nat_add_one_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [Function.comp_def, Nat.cast_succ] using h.comp_injective Nat.succ_injective

theorem dyadic_weight_summable (c : ℝ) :
    Summable (fun m => dyadicRadius m ^ 2 * dyadicSlope c m ^ 2) := by
  simp_rw [dyadic_weight_identity]
  exact summable_one_div_nat_add_one_sq.mul_left _

theorem dyadic_weight_total (c : ℝ) :
    (∑' m, dyadicRadius m ^ 2 * dyadicSlope c m ^ 2) =
      (c ^ 2 / 64) * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
  simp_rw [dyadic_weight_identity]
  exact tsum_mul_left

theorem reciprocalSquare_step (m : ℕ) :
    1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) := by
  have h : 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    one_div_le_one_div_of_le
      (show (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2) from by positivity)
      (show ((m : ℝ) + 1) * ((m : ℝ) + 2) ≤ ((m : ℝ) + 2) ^ 2 from by
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have heq : 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) =
      1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) := by
    have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h1, h2]
    ring
  exact h.trans_eq heq

theorem reciprocalSquare_partial (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), 1 / ((m : ℝ) + 1) ^ 2) ≤ 2 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := reciprocalSquare_step N
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith

theorem tsum_one_div_nat_add_one_sq_le_two : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) ≤ 2 := by
  apply le_of_tendsto' summable_one_div_nat_add_one_sq.hasSum.tendsto_sum_nat
  intro N
  cases N with
  | zero => simp
  | succ N =>
    exact (reciprocalSquare_partial N).trans (by
      have h : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith)

/-- R6's global squared-weight budget c²/32, with the full reciprocal-square sum. -/
theorem dyadic_weight_total_le (c : ℝ) :
    (∑' m, dyadicRadius m ^ 2 * dyadicSlope c m ^ 2) ≤ c ^ 2 / 32 := by
  rw [dyadic_weight_total]
  calc
    (c ^ 2 / 64) * (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) ≤ (c ^ 2 / 64) * 2 :=
      mul_le_mul_of_nonneg_left tsum_one_div_nat_add_one_sq_le_two (by positivity)
    _ = c ^ 2 / 32 := by ring

end BanachGeometry.HilbertSums
