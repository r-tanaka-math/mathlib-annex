import BanachGeometry.SequenceSpaces.UnitBall

/-! Approximate norming on the actual closed unit ball. No norm
attainment of a dual functional is assumed.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace UnitBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eval_gt (f : E →L[ℝ] ℝ) (t : ℝ) (ht : t < ‖f‖) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ t < f x := by
  by_cases ht0 : t < 0
  · exact ⟨0,by simp,by simpa using ht0⟩
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    by_contra! h
    have hn : ‖f‖ ≤ t := by
      apply opNorm_le f t ht0'
      intro x hx
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      refine ⟨?_,h x hx⟩
      have he := h (-x) (by simpa only [norm_neg] using hx)
      rw [map_neg] at he
      linarith
    exact ht.not_ge hn

theorem exists_scaled_norm_eval (f : E →L[ℝ] ℝ) (α : ℝ) (hα : α < 1) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ α * ‖f‖ ≤ f x := by
  by_cases hf : ‖f‖ = 0
  · refine ⟨0,by simp,?_⟩
    simp [hf]
  · have hp : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf)
    have ht : α * ‖f‖ < ‖f‖ := by nlinarith [mul_pos (sub_pos.mpr hα) hp]
    obtain ⟨x,hx,hfx⟩ := exists_eval_gt f _ ht
    exact ⟨x,hx,hfx.le⟩

end UnitBall
end BanachGeometry
