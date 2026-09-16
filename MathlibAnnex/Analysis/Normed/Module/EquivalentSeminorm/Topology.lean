import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Topology and comparison estimates for equivalent seminorms -/

namespace MathlibAnnex.EquivalentSeminorm

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (M : EquivalentSeminorm E)

/-- The model unit ball is bounded for the reference norm. -/
theorem closedUnitBall_isBounded : Bornology.IsBounded M.closedUnitBall := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
  refine ⟨1 / M.lower, ?_⟩
  intro x hx
  have hprod : M.lower * ‖x‖ ≤ 1 :=
    (M.lower_le x).trans (M.mem_closedUnitBall.mp hx)
  have hnorm : ‖x‖ ≤ 1 / M.lower := by
    apply (le_div_iff₀ M.lower_pos).2
    nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Finite dimensional model unit balls are compact, including dimension zero. -/
theorem closedUnitBall_isCompact [FiniteDimensional ℝ E] :
    IsCompact M.closedUnitBall := by
  apply Metric.isCompact_of_isClosed_isBounded _ M.closedUnitBall_isBounded
  change IsClosed (M.p.closedBall 0 1)
  have h : M.p.closedBall 0 1 = {x : E | M.p x ≤ 1} := by ext x; simp
  rw [h]
  exact isClosed_le M.continuous_p continuous_const

/-- The origin is an interior point of the model unit ball. -/
theorem zero_mem_interior_closedUnitBall : (0 : E) ∈ interior M.closedUnitBall := by
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : E) (one_div_pos.mpr M.upper_pos)) ?_
  intro x hx
  have hnorm : ‖x‖ < 1 / M.upper := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hprod : M.upper * ‖x‖ < 1 := by
    have := (lt_div_iff₀ M.upper_pos).1 hnorm
    nlinarith
  exact M.mem_closedUnitBall.mpr ((M.le_upper x).trans hprod.le)

/-- A model increment bound gives the stored upper Lipschitz constant. -/
theorem lipschitzWith_upper_of_model_bound {f : E → F}
    (hf : ∀ x y, ‖f x - f y‖ ≤ M.p (x - y)) :
    LipschitzWith M.upper.toNNReal f := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  calc
    dist (f x) (f y) = ‖f x - f y‖ := by simp [dist_eq_norm]
    _ ≤ M.p (x - y) := hf x y
    _ ≤ M.upper * ‖x - y‖ := M.le_upper (x - y)
    _ = (M.upper.toNNReal : ℝ) * dist x y := by
      rw [Real.coe_toNNReal M.upper M.upper_pos.le, dist_eq_norm]

end MathlibAnnex.EquivalentSeminorm
