import BanachGeometry.AlmostIsometric.HilbertFreeSpaceDataViaCoordinates
/- Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry
open scoped NNReal

open BanachGeometry BanachGeometry.HilbertSums LipschitzFreeProperties
open BanachGeometry.LipschitzFreeGeometry.FreeSpace (Space point supported)

example {M B : Type*} [MetricSpace M] [Zero M]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (g : M → B) {L : ℝ≥0} (hg : LipschitzWith L g) (hg0 : g 0 = 0) :
    ∃! T : Space M →L[ℝ] B, (∀ x, T (point x) = g x) ∧
      IsLeast {K : ℝ≥0 | LipschitzWith K g} ‖T‖₊ :=
  existsUnique_linearization g hg hg0

example {M : Type*} [MetricSpace M] [Zero M] [CompleteSpace M]
    (μ : ℕ → Space M) (hμ : WeakNull μ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧ ∃ ν : ℕ → Space M,
      (∀ n, ν n ∈ supported K) ∧ (∀ n, ‖μ n - ν n‖ < τ) ∧
      (∀ n, ‖ν n‖ ≤ (⨆ j, ‖μ j‖) + τ) :=
  exists_compact_approximation_with_iSup_norm μ hμ hτ

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    ¬ ContainsLinearCopy ScalarC0 (Space H) := hilbert_free_no_c0

example : HasQuantitativeHilbertModels := exists_quantitativeHilbertData
example : HasQuantitativeHilbertModels := exists_quantitativeHilbertData_via_coordinates

-- The recommended and legacy routes carry identical mathematical data.
-- Their complete-continuity proofs may use different localization theorems.
example (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    (hilbertFreeSpaceData c hc hc').d = (coordinateHilbertFreeSpaceData c hc hc').d := rfl
example (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    (hilbertFreeSpaceData c hc hc').linearMap = (coordinateHilbertFreeSpaceData c hc hc').linearMap := rfl
example (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    (hilbertFreeSpaceData c hc hc').h = (coordinateHilbertFreeSpaceData c hc hc').h := rfl

#check Nonlinear.recursive_radicand_eq_norm_blockTail_sq
#check Nonlinear.recursive_radicand_nonneg
#check Nonlinear.inverseHilbertMap_surjective
