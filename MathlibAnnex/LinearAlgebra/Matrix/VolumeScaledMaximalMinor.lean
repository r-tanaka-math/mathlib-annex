import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import MathlibAnnex.MeasureTheory.Measure.EquivalentSeminormBall
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Maximal minors scaled by model ball volume

Rows use the increasing order fixed by `MaximalMinorIndex`. Pairing is the
ordinary real `dotProduct`, with no change of orientation or normalization.
-/

noncomputable section

namespace MathlibAnnex.Matrix

open scoped BigOperators

/-- The maximal-minor vector multiplied by the model ball's Lebesgue volume. -/
def ballVolumeScaledMaximalMinors {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) : MaximalMinorIndex n (Fin N) → ℝ :=
  M.closedUnitBallVolume • maximalMinors (LinearMap.toMatrix' A.toLinearMap)

@[simp] theorem ballVolumeScaledMaximalMinors_zero_of_pos {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (hn : 0 < n) :
    ballVolumeScaledMaximalMinors M (0 : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) = 0 := by
  simp [ballVolumeScaledMaximalMinors, maximalMinors_zero_of_pos hn]

theorem pairing_ballVolumeScaledMaximalMinors {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (w : MaximalMinorIndex n (Fin N) → ℝ)
    (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) :
    dotProduct w (ballVolumeScaledMaximalMinors M A) =
      M.closedUnitBallVolume * dotProduct w (maximalMinors (LinearMap.toMatrix' A.toLinearMap)) := by
  simp only [dotProduct, ballVolumeScaledMaximalMinors, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem continuous_toMatrix' {n N : ℕ} :
    Continuous (fun A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ) =>
      LinearMap.toMatrix' A.toLinearMap) := by
  apply continuous_matrix
  intro i j
  change Continuous fun A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ) => A (Pi.single j 1) i
  fun_prop

/-- Continuity of the volume-scaled maximal-minor vector. -/
theorem continuous_ballVolumeScaledMaximalMinors {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) :
    Continuous (ballVolumeScaledMaximalMinors M :
      ((Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) → (MaximalMinorIndex n (Fin N) → ℝ)) := by
  change Continuous fun A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ) =>
    M.closedUnitBallVolume • maximalMinors (LinearMap.toMatrix' A.toLinearMap)
  exact continuous_const.smul (maximalMinors_continuous.comp continuous_toMatrix')

end MathlibAnnex.Matrix
