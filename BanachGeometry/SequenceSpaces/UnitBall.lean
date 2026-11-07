import BanachGeometry.Basic
import Mathlib.Tactic

/-! Actual unit-ball normalization and approximate norming vectors. These
lemmas assume no norm attainment.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace UnitBall
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem opNorm_le (T : E →L[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : E, ‖x‖ ≤ 1 → ‖T x‖ ≤ C) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro x
  by_cases hx : x = 0
  · subst x; simp
  · have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
    have hb := h (‖x‖⁻¹ • x) hu
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] at hb
    have hd : ‖T x‖ / ‖x‖ ≤ C := by simpa only [div_eq_mul_inv, mul_comm] using hb
    exact (div_le_iff₀ hp).mp hd

theorem exists_half_norm_eval (f : E →L[ℝ] ℝ) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f‖ ≤ 2 * f x := by
  by_cases hf : ‖f‖ = 0
  · exact ⟨0, by simp, by simp [hf]⟩
  · have hp : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    have hex : ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f‖ / 2 < ‖f x‖ := by
      by_contra hbad
      push_neg at hbad
      have hsmall := opNorm_le f (‖f‖ / 2) (by positivity) hbad
      linarith
    obtain ⟨x, hx, hfx⟩ := hex
    by_cases hneg : f x < 0
    · refine ⟨-x, by simpa only [norm_neg] using hx, ?_⟩
      rw [map_neg]
      rw [Real.norm_eq_abs, abs_of_neg hneg] at hfx
      linarith
    · refine ⟨x, hx, ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_not_gt hneg)] at hfx
      linarith

theorem exists_small_unit (T : E →L[ℝ] F) (ε : ℝ)
    (h : ¬ ∀ x, ε * ‖x‖ ≤ ‖T x‖) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  push_neg at h
  obtain ⟨x, hx⟩ := h
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr (by intro hzero; simp [hzero] at hx)
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  · rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    apply (inv_mul_lt_iff₀ hp).mpr
    nlinarith

end UnitBall
end BanachGeometry
