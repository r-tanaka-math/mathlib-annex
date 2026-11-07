import BanachGeometry.Complemented.HeadSplitting
import BanachGeometry.AlmostIsometric.FamilyFromHilbertData

/-! Quantitative Hilbert data yield the fixed pair under explicit finite-sum
exclusion h4. The metric family, complemented copies H2 and coordinate
splittings H3 are constructed in FamilyFromHilbertData. NoC0Closure proves
h4 for these sequences and applies this reduction; Existence supplies the
concrete quantitative Hilbert models without an additional theorem input. -/
noncomputable section
namespace BanachGeometry
namespace QuantitativeHilbertSequence

theorem exists_almostIsometric_nonisomorphic_pair_of_finite_exclusion (s : QuantitativeHilbertSequence) (h4 : s.metricFamily.ExcludesFiniteSumCopy) : ExistsAlmostIsometricNonisomorphicPair :=
  s.metricFamily.exists_almostIsometric_nonisomorphic_pair_of_complemented_splitting_exclusion s.hasContractivelyComplementedCopy_metricFamily s.hasCoordinateSplitting_metricFamily h4

end QuantitativeHilbertSequence
end BanachGeometry
