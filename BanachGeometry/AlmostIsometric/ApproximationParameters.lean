import BanachGeometry.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! R6 §7 parameters with precisely the zero-based shifts of the common
contract. All sequences are fixed before the final metric tolerance. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace ApproximationParameters

def c (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 5)
def theta (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)
def weight (n m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + m + 2)
def lower (n : ℕ) : ℝ := 1 - 4 * c n
def upper (n : ℕ) : ℝ := 1 + 4 * c n
def bound (n : ℕ) : ℝ :=
  max 1 (max (1 + theta n) (max (upper n)
    (max (1 + 2 * theta n / lower n) (lower n)⁻¹)))

theorem half_pow_le_one (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

theorem c_pos (n : ℕ) : 0 < c n := by unfold c; positivity
theorem c_le (n : ℕ) : c n ≤ 1 / 32 := by
  unfold c
  rw [pow_add]
  norm_num
  nlinarith [half_pow_le_one n]

theorem c_lt_quarter (n : ℕ) : c n < 1 / 4 := by linarith [c_le n]
theorem theta_pos (n : ℕ) : 0 < theta n := by unfold theta; positivity
theorem theta_le_one (n : ℕ) : theta n ≤ 1 := half_pow_le_one (n + 1)
theorem weight_pos (n m : ℕ) : 0 < weight n m := by unfold weight; positivity
theorem lower_pos (n : ℕ) : 0 < lower n := by unfold lower; linarith [c_le n]

theorem weight_factor (n m : ℕ) : weight n m = theta n * (1 / 2 : ℝ) ^ (m + 1) := by
  unfold weight theta
  rw [← pow_add]
  congr 1
  omega

theorem weight_summable (n : ℕ) : Summable (weight n) := by
  change Summable (fun m => weight n m)
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).summable
  have hs : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) := by
    simpa only [pow_succ] using hg.mul_right (1 / 2 : ℝ)
  simpa only [weight_factor] using hs.mul_left (theta n)

theorem weights_sum (n : ℕ) : (∑' m, weight n m) = theta n := by
  have hshift : (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) = 1 := by
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num
  simp_rw [weight_factor]
  rw [tsum_mul_left, hshift, mul_one]

theorem c_tendsto : Tendsto c atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp
    (tendsto_add_atTop_nat 5)

theorem theta_tendsto : Tendsto theta atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp
    (tendsto_add_atTop_nat 1)

theorem lower_tendsto : Tendsto lower atTop (nhds 1) := by
  change Tendsto (fun n => 1 - 4 * c n) atTop (nhds 1)
  simpa only [lower, mul_zero, sub_zero] using
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul c_tendsto) :
      Tendsto (fun n => 1 - 4 * c n) atTop (nhds (1 - 4 * 0)))

theorem upper_tendsto : Tendsto upper atTop (nhds 1) := by
  change Tendsto (fun n => 1 + 4 * c n) atTop (nhds 1)
  simpa only [upper, mul_zero, add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul c_tendsto) :
      Tendsto (fun n => 1 + 4 * c n) atTop (nhds (1 + 4 * 0)))

theorem one_le_bound (n : ℕ) : 1 ≤ bound n := le_max_left _ _

theorem bound_tendsto : Tendsto bound atTop (nhds 1) := by
  have hθ : Tendsto (fun n => 1 + theta n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add theta_tendsto
  have hr : Tendsto (fun n => 2 * theta n / lower n) atTop (nhds 0) := by
    change Tendsto ((fun n => 2 * theta n) / lower) atTop (nhds 0)
    simpa using (tendsto_const_nhds.mul theta_tendsto).div lower_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  have hf : Tendsto (fun n => 1 + 2 * theta n / lower n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hr
  have hi : Tendsto (fun n => (lower n)⁻¹) atTop (nhds 1) := by
    simpa using lower_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun n => max 1 (max (1 + theta n) (max (upper n)
    (max (1 + 2 * theta n / lower n) (lower n)⁻¹)))) atTop (nhds 1)
  simpa only [max_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).max
      (hθ.max (upper_tendsto.max (hf.max hi)))

theorem models_at_parameters (supply : HasQuantitativeHilbertModels) (n : ℕ) :
    ∃ A : SeparableRealBanach, ∃ H : SeparableRealHilbert, Nonempty (QuantitativeHilbertData (c n) A H) :=
  supply (c n) (c_pos n) (c_lt_quarter n)

end ApproximationParameters
end BanachGeometry
