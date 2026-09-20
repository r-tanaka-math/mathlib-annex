import MathlibAnnex.Analysis.Convex.PluckerBody
import MathlibAnnex.Analysis.Calculus.FDeriv.SeminormBound
import Mathlib.Analysis.Convex.Integral

/-!
# Derivative generators and their average

The generator uses the original Lebesgue ball volume and increasing-row maximal
minors. Averaging over the same closed ball preserves membership in the convex
body. All statements include dimension zero and empty maximal-minor index sets.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace MathlibAnnex.Plucker

/-- The volume-scaled maximal-minor vector of a Fréchet derivative. -/
def derivativeGenerator {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin N → ℝ)) (x : Fin n → ℝ) :
    Matrix.MaximalMinorIndex n (Fin N) → ℝ :=
  Matrix.ballVolumeScaledMaximalMinors M (fderiv ℝ f x)

/-- The set average of derivative generators over the model closed unit ball. -/
def derivativeAverage {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin N → ℝ)) :
    Matrix.MaximalMinorIndex n (Fin N) → ℝ :=
  ⨍ x in M.closedUnitBall, derivativeGenerator M f x ∂volume

/-- A contractive derivative is a positive raw generator. -/
theorem derivativeGenerator_mem_raw {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin N → ℝ)) {x : Fin n → ℝ}
    (hx : M.IsContraction (fderiv ℝ f x)) :
    derivativeGenerator M f x ∈ PluckerBody.generators M N := by
  exact ⟨fderiv ℝ f x, hx, Or.inl rfl⟩

/-- The average of integrable, almost everywhere contractive derivative
generators belongs to the model Plücker body. -/
theorem derivativeAverage_mem_body {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hcontract : ∀ᵐ x ∂volume.restrict M.closedUnitBall,
      M.IsContraction (fderiv ℝ f x))
    (hint : IntegrableOn (derivativeGenerator M f) M.closedUnitBall volume) :
    derivativeAverage M f ∈ PluckerBody.body M N := by
  have hzero : volume M.closedUnitBall ≠ 0 := by
    intro h
    have hp := M.closedUnitBallVolume_pos
    simp [EquivalentSeminorm.closedUnitBallVolume, h] at hp
  apply (convex_convexHull ℝ (PluckerBody.generators M N)).set_average_mem
    (isCompact_convexHull_pi _ (PluckerBody.isCompact_generators M)).isClosed
    hzero M.isCompact_closedUnitBall.measure_ne_top
  · filter_upwards [hcontract] with x hx
    exact subset_convexHull ℝ _ (derivativeGenerator_mem_raw M f hx)
  · exact hint

/-- A global seminorm increment bound gives integrability on the model ball. -/
theorem integrableOn_derivativeGenerator_of_seminormLipschitz {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hf : ∀ x y, ‖f x - f y‖ ≤ M.p (x - y)) :
    IntegrableOn (derivativeGenerator M f) M.closedUnitBall volume := by
  have hmeas : StronglyMeasurable (derivativeGenerator M f) :=
    ((Matrix.continuous_ballVolumeScaledMaximalMinors M).measurable.comp
      (measurable_fderiv ℝ f)).stronglyMeasurable
  have hcontract : ∀ᵐ x ∂volume.restrict M.closedUnitBall,
      M.IsContraction (fderiv ℝ f x) :=
    FDeriv.ae_norm_apply_le_seminorm_of_lipschitz M.p
      ⟨M.upper, M.upper_pos.le⟩ M.le_upper hf M.closedUnitBall
  rcases (PluckerBody.isCompact_generators (N := N) M).isBounded.subset_closedBall
      (0 : Matrix.MaximalMinorIndex n (Fin N) → ℝ) with ⟨C, hC⟩
  have hnorm : ∀ᵐ x ∂volume.restrict M.closedUnitBall,
      ‖derivativeGenerator M f x‖ ≤ max C 0 := by
    filter_upwards [hcontract] with x hx
    have hfxC : ‖derivativeGenerator M f x‖ ≤ C := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        hC (derivativeGenerator_mem_raw M f hx)
    exact hfxC.trans (le_max_left _ _)
  exact IntegrableOn.of_bound
    (lt_top_iff_ne_top.mpr M.isCompact_closedUnitBall.measure_ne_top)
    hmeas.aestronglyMeasurable (max C 0) hnorm

/-- An ordinary Lipschitz map has integrable derivative generators on every
compact subset of its finite-dimensional source. -/
theorem integrableOn_derivativeGenerator_compact {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hf : ∃ C : NNReal, LipschitzWith C f) {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    IntegrableOn (derivativeGenerator M f) K volume := by
  rcases hf with ⟨C, hC⟩
  let D : Set ((Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) := Metric.closedBall 0 (C : ℝ)
  have hD : IsCompact D := by
    simpa [D] using
      (isCompact_closedBall (0 : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (C : ℝ))
  have hP : IsCompact (Matrix.ballVolumeScaledMaximalMinors M '' D) :=
    hD.image (Matrix.continuous_ballVolumeScaledMaximalMinors M)
  have hmeas : StronglyMeasurable (derivativeGenerator M f) :=
    ((Matrix.continuous_ballVolumeScaledMaximalMinors M).measurable.comp
      (measurable_fderiv ℝ f)).stronglyMeasurable
  have hmem : ∀ᵐ x ∂volume.restrict K,
      derivativeGenerator M f x ∈ Matrix.ballVolumeScaledMaximalMinors M '' D :=
    Filter.Eventually.of_forall fun x => by
      refine ⟨fderiv ℝ f x, ?_, rfl⟩
      change fderiv ℝ f x ∈ Metric.closedBall 0 (C : ℝ)
      rw [Metric.mem_closedBall]
      simpa [dist_zero_right] using (norm_fderiv_le_of_lipschitz ℝ hC (x₀ := x))
  rcases hP.isBounded.subset_closedBall
      (0 : Matrix.MaximalMinorIndex n (Fin N) → ℝ) with ⟨B, hB⟩
  have hnorm : ∀ᵐ x ∂volume.restrict K, ‖derivativeGenerator M f x‖ ≤ max B 0 := by
    filter_upwards [hmem] with x hx
    have hfxB : ‖derivativeGenerator M f x‖ ≤ B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB hx
    exact hfxB.trans (le_max_left _ _)
  exact IntegrableOn.of_bound (lt_top_iff_ne_top.mpr hK.measure_ne_top)
    hmeas.aestronglyMeasurable (max B 0) hnorm

end MathlibAnnex.Plucker
