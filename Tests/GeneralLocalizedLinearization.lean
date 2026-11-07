import BanachGeometry.LipschitzFreeSpace.Localization.Auxiliary
import BanachGeometry.LipschitzFreeSpace.Localization.ScalarTests
import BanachGeometry.LipschitzFreeSpace.Localization.OrderedLimsup
/- Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry
open scoped NNReal
open BanachGeometry BanachGeometry.HilbertSums LipschitzFreeLocalization

#check tendsto_zero_of_weakNull_finiteDimensional
#check tendsto_norm_starProjection_zero
#check badSet_finite_of_incrementLocality
#check exists_compact_good_subsequence
#check eventually_pairing_bound_on_compact
#check summableTestOperator_coord
#check ordered_shrinking_tests
#check compact_patch_lipschitzOn
#check completelyContinuous_linearize_of_incrementLocality
#check incrementLocality_of_coordinateLocalOrthogonality

example {M H : Type*} [MetricSpace M] [Zero M] [CompleteSpace M]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : IncrementLocality D) :
    CompletelyContinuous (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D) :=
  completelyContinuous_linearize_of_incrementLocality D hD hD0 hloc

example : HasQuantitativeHilbertModels := exists_quantitativeHilbertData
#check LipschitzFreeLocalization.tendsto_shrinkingPairingLimsup_zero
