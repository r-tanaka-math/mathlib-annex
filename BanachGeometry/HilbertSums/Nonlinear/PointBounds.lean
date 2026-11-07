/- Fixed-radius point bound, then the actual tail-dependent direction bound.
Normalization uses the same exact denominator at both points, avoiding a lost factor 2.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.TailEnergy
import BanachGeometry.HilbertSums.ScaleClock.Order

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear
open Coding Clock

/-- Exact interpolation estimate in two fixed orthogonal subspaces. -/
theorem unitSegment_point_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v u' v' : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (huv' : ⟪u', v'⟫_ℝ = 0)
    (hdiff : ⟪u - u', v - v'⟫_ℝ = 0) (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (h₁ : ‖u - u'‖ ≤ M * D) (h₂ : ‖v - v'‖ ≤ M * D) (s : ℝ) :
    ‖unitSegment u v s - unitSegment u' v' s‖ ≤ M * D := by
  let a := affineSegment u v s
  let b := affineSegment u' v' s
  have ha : a ≠ 0 := affineSegment_ne_zero _ _ hu hv huv s
  have he : ‖a‖ = ‖b‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
    rw [norm_affineSegment_sq _ _ hu hv huv, norm_affineSegment_sq _ _ hu' hv' huv'])
  have hid : a - b = (1 - s) • (u - u') + s • (v - v') := by dsimp [a, b, affineSegment]; module
  have hsq : ‖a - b‖ ^ 2 = (1 - s) ^ 2 * ‖u - u'‖ ^ 2 + s ^ 2 * ‖v - v'‖ ^ 2 := by
    rw [hid, norm_add_sq_real]
    simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right, hdiff]
  have h₁sq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hD)).2 h₁
  have h₂sq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hD)).2 h₂
  have hsum : ‖a - b‖ ^ 2 ≤ ‖a‖ ^ 2 * (M * D) ^ 2 := by
    rw [hsq, norm_affineSegment_sq _ _ hu hv huv]
    nlinarith [mul_le_mul_of_nonneg_left h₁sq (sq_nonneg (1 - s)),
      mul_le_mul_of_nonneg_left h₂sq (sq_nonneg s)]
  have hscaled : ‖a‖ * ‖unitSegment u v s - unitSegment u' v' s‖ = ‖a - b‖ := by
    have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    change ‖a‖ * ‖NormedSpace.normalize a - NormedSpace.normalize b‖ = _
    rw [NormedSpace.normalize, NormedSpace.normalize, ← he, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg a)]
    field_simp [hn]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hD)).1
  have hscaledSq := congrArg (fun t : ℝ => t ^ 2) hscaled
  rw [mul_pow] at hscaledSq
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp
  rw [hscaledSq]
  exact hsum

theorem bridge_point_bound (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n)
    (y z : GradedHilbert) (t : ℝ) :
    ‖bridge c hc n k hk y t - bridge c hc n k hk z t‖ ≤
      max (codeLipschitz k) (codeLipschitz (k + 1)) * ‖y - z‖ := by
  have h₁ := codeDirection_norm_sub_le n k (by omega) y z
  have h₂ := codeDirection_norm_sub_le n (k + 1) (by omega) y z
  have hdiff : ⟪codeDirection n k (by omega) y - codeDirection n k (by omega) z,
      codeDirection n (k + 1) (by omega) y - codeDirection n (k + 1) (by omega) z⟫_ℝ = 0 := by
    simp only [codeDirection, ← (levelIsometry _ _ _).map_sub]
    exact level_inner_ne _ _ _ _ _ (by omega) _ _
  apply unitSegment_point_bound _ _ _ _ (norm_codeDirection _ _ _ _) (norm_codeDirection _ _ _ _)
    (norm_codeDirection _ _ _ _) (norm_codeDirection _ _ _ _)
    (level_inner_ne _ _ _ _ _ (by omega) _ _) (level_inner_ne _ _ _ _ _ (by omega) _ _)
    hdiff _ _ (by unfold codeLipschitz; positivity) (norm_nonneg _)
    (h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    (h₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

theorem omegaPrefix_point_bound (c : ℝ) (hc : 0 < c) (n : ℕ) (y z : GradedHilbert)
    {r : ℝ} (hr : 0 < r) : ∀ k (hk : k ≤ n),
    ‖omegaPrefix c hc n y (tau c r) k hk - omegaPrefix c hc n z (tau c r) k hk‖ ≤
      gamma c r / 2 * ‖y - z‖ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 := codeDirection_norm_sub_le n 0 (by omega) y z
    simp only [codeLipschitz, Nat.cast_zero, mul_zero, zero_mul] at h0
    exact h0.trans (mul_nonneg (div_nonneg (gamma_nonneg hc.le r) (by norm_num)) (norm_nonneg _))
  | succ k ih =>
    intro hk
    rw [omegaPrefix, omegaPrefix]
    split_ifs with ht
    · exact ih _
    · have hbudget := active_transition_budget c hc k hr (le_of_not_ge ht)
      exact (bridge_point_bound c hc n k hk y z _).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

theorem omega_point_bound (c : ℝ) (hc : 0 < c) (n : ℕ) (y z : GradedHilbert)
    {r : ℝ} (hr : 0 < r) :
    ‖omega c hc n y r - omega c hc n z r‖ ≤ gamma c r / 2 * ‖y - z‖ := by
  rw [omega, if_pos hr, omega, if_pos hr]
  exact omegaPrefix_point_bound c hc n y z hr n le_rfl

/-- Both radii must be positive; zero radii are handled by the vanishing weight. -/
theorem pointDirection_difference_bound (c : ℝ) (hc : 0 < c) (y z : GradedHilbert) (n : ℕ)
    (hy : 0 < ‖blockTail n y‖) (hz : 0 < ‖blockTail n z‖) :
    ‖pointDirection c hc y n - pointDirection c hc z n‖ ≤
      gamma c (min ‖blockTail n y‖ ‖blockTail n z‖) * ‖y - z‖ := by
  let r := ‖blockTail n y‖
  let s := ‖blockTail n z‖
  have h₁ := omega_point_bound c hc n y z hy
  have h₂ := omega_radius_bound c hc n z hy hz
  have hrad := abs_norm_blockTail_sub_norm_blockTail_le n y z
  have hgamma : gamma c r ≤ gamma c (min r s) := gamma_antitone_positive hc.le
    (lt_min hy hz) hy (min_le_left _ _)
  have h₃ := mul_le_mul_of_nonneg_right hgamma (norm_nonneg (y - z))
  have h₄ := mul_le_mul_of_nonneg_left hrad
    (div_nonneg (gamma_nonneg hc.le (min r s)) (by norm_num : (0 : ℝ) ≤ 2))
  have ht := norm_sub_le_norm_sub_add_norm_sub (omega c hc n y r) (omega c hc n z r) (omega c hc n z s)
  change ‖omega c hc n y r - omega c hc n z s‖ ≤ _
  dsimp [r, s] at *
  linarith

end BanachGeometry.HilbertSums.Nonlinear
