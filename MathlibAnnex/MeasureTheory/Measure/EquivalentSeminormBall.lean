import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Lebesgue volume of an equivalent seminorm ball

This API uses the original Lebesgue volume on finite real Pi coordinates.
Its normalization is fixed; the measure is not an arbitrary rescaled Haar measure.
-/

namespace MathlibAnnex.EquivalentSeminorm

open MeasureTheory

variable {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))

/-- Real Lebesgue volume of the model closed unit ball. -/
noncomputable def closedUnitBallVolume : ℝ := (volume M.closedUnitBall).toReal

/-- The model ball has finite positive volume, also when `n = 0`. -/
theorem closedUnitBallVolume_pos : 0 < M.closedUnitBallVolume := by
  unfold closedUnitBallVolume
  have hpos : volume M.closedUnitBall ≠ 0 :=
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior volume
      ⟨0, M.zero_mem_interior_closedUnitBall⟩).ne'
  have htop : volume M.closedUnitBall ≠ ⊤ := M.closedUnitBall_isCompact.measure_ne_top
  exact ENNReal.toReal_pos hpos htop

end MathlibAnnex.EquivalentSeminorm
