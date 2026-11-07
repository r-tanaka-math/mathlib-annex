import BanachGeometry.AlmostIsometric.FromQuantitativeHilbertData
import BanachGeometry.OperatorGraphs.FiniteGraph

/-! Basis decay excludes finite Hilbert-graph sums and yields the almost-isometric
nonisomorphic conclusion. The abstract basis-decay implication is an explicit
hypothesis only in the final generic helper, not in the concrete existence theorem. -/
noncomputable section
namespace BanachGeometry
namespace QuantitativeHilbertSequence

theorem excludesFiniteSumCopy_of_basisDecay (s : QuantitativeHilbertSequence)
    (hdecay : ∀ n, BasisDecay (s.A n).Carrier) : s.metricFamily.ExcludesFiniteSumCopy := by
  intro q indices
  change ¬ ContainsLinearCopy C0L2 (∀ r : Fin q,
    OperatorGraphPair.Y (s.input (indices r)) (ApproximationParameters.weight (indices r)))
  exact WeightedGraph.finite_no_c0L2_of_basisDecay q
    (fun r _ => (s.A (indices r)).Carrier) (fun r _ => (s.H (indices r)).Carrier)
    (fun r _ => (s.input (indices r)).linearMap) (fun r => ApproximationParameters.weight (indices r))
    (fun r => ApproximationParameters.weight_pos (indices r))
    (fun r _ => (s.input (indices r)).linearMap_completelyContinuous)
    (fun r _ => hdecay (indices r))

theorem exists_almostIsometric_nonisomorphic_pair_of_basisDecay (s : QuantitativeHilbertSequence)
    (hdecay : ∀ n, BasisDecay (s.A n).Carrier) : ExistsAlmostIsometricNonisomorphicPair :=
  s.exists_almostIsometric_nonisomorphic_pair_of_finite_exclusion (s.excludesFiniteSumCopy_of_basisDecay hdecay)

end QuantitativeHilbertSequence

/-- Generic implication for separable Banach bundles with explicit basis-decay input. -/
theorem exists_almostIsometric_nonisomorphic_pair_of_exists_quantitativeHilbertData_via_coordinates_and_basisDecay (supply : HasQuantitativeHilbertModels)
    (hBP : ∀ E : SeparableRealBanach,
      ¬ ContainsLinearCopy ScalarC0 E.Carrier → BasisDecay E.Carrier) : ExistsAlmostIsometricNonisomorphicPair := by
  let s := QuantitativeHilbertSequence.ofModels supply
  exact s.exists_almostIsometric_nonisomorphic_pair_of_basisDecay (fun n => hBP (s.A n) (s.input n).no_c0)

end BanachGeometry
