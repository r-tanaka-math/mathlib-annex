import BanachGeometry.OperatorGraphs.GraphBounds
import BanachGeometry.AlmostIsometric.ApproximationParameters
import BanachGeometry.AlmostIsometric.CriterionAssembly

/-! A fixed family from quantitative Hilbert models, with its spaces and norms chosen
once before ε. This module supplies contractively complemented copies and coordinate
splittings. Finite-sum exclusion is proved downstream in NoC0/NoC0Closure and
assembled with these results in AlmostIsometric/Existence.
Execution evidence is recorded in the external receipts. -/

noncomputable section
namespace BanachGeometry
namespace ApproximationParameters

theorem graph_forwardConstant_le_bound (n : ℕ) :
    GraphBounds.forwardConstant (c := c n) (weight n) ≤ bound n := by
  rw [GraphBounds.forwardConstant, weights_sum]
  change max (1 + theta n) (1 + 4 * c n) ≤
    max 1 (max (1 + theta n) (max (1 + 4 * c n)
      (max (1 + 2 * theta n / lower n) (lower n)⁻¹)))
  exact max_le (le_max_of_le_right (le_max_left _ _))
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

theorem graph_inverseConstant_le_bound (n : ℕ) :
    GraphBounds.inverseConstant (c := c n) (weight n) ≤ bound n := by
  rw [GraphBounds.inverseConstant, weights_sum]
  change max (1 + 2 * theta n / lower n) (lower n)⁻¹ ≤
    max 1 (max (1 + theta n) (max (upper n)
      (max (1 + 2 * theta n / lower n) (lower n)⁻¹)))
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl))

end ApproximationParameters

structure QuantitativeHilbertSequence where
  A : ℕ → SeparableRealBanach
  H : ℕ → SeparableRealHilbert
  input : ∀ n, QuantitativeHilbertData (ApproximationParameters.c n) (A n) (H n)

namespace QuantitativeHilbertSequence

def ofModels (supply : HasQuantitativeHilbertModels) : QuantitativeHilbertSequence := by
  choose A H h using ApproximationParameters.models_at_parameters supply
  exact ⟨A, H, fun n => Classical.choice (h n)⟩

def metricFamily (d : QuantitativeHilbertSequence) : AlmostIsometricFamily where
  X n := OperatorGraphPair.xBanach (d.input n) (ApproximationParameters.weight n) (ApproximationParameters.weight_pos n)
  Y n := OperatorGraphPair.yBanach (d.input n) (ApproximationParameters.weight n) (ApproximationParameters.weight_pos n)
  bound := ApproximationParameters.bound
  one_le := ApproximationParameters.one_le_bound
  tends_one := ApproximationParameters.bound_tendsto
  psi n := GraphBounds.pointed (d.input n) (ApproximationParameters.weight n)
    (ApproximationParameters.weight_pos n) (ApproximationParameters.weight_summable n)
    (ApproximationParameters.c_pos n).le (ApproximationParameters.lower_pos n) (ApproximationParameters.bound n)
    (ApproximationParameters.graph_forwardConstant_le_bound n) (ApproximationParameters.graph_inverseConstant_le_bound n)

theorem hasContractivelyComplementedCopy_metricFamily (d : QuantitativeHilbertSequence) : d.metricFamily.HasContractivelyComplementedCopy := by
  intro n
  exact OperatorGraphPair.isometric_complemented (d.input n) (ApproximationParameters.weight n)
    (ApproximationParameters.weight_pos n) (ApproximationParameters.weight_summable n)
    (by rw [ApproximationParameters.weights_sum]; exact ApproximationParameters.theta_le_one n)

theorem hasCoordinateSplitting_metricFamily (d : QuantitativeHilbertSequence) : d.metricFamily.HasCoordinateSplitting := by
  intro n
  exact ⟨OperatorGraphPair.splitting (d.input n) (ApproximationParameters.weight n)
    (ApproximationParameters.weight_pos n) (ApproximationParameters.weight_summable n)
    (by rw [ApproximationParameters.weights_sum]; exact ApproximationParameters.theta_le_one n)⟩

end QuantitativeHilbertSequence

/-- A HasQuantitativeHilbertModels input yields a family with complemented
copies H2 and coordinate splittings H3. NoC0Closure proves finite-sum exclusion
H4 for the same QuantitativeHilbertSequence; Existence combines these results.
The local conclusion here consists of H2 and H3 only. -/
theorem metricFamily_complemented_splitting_of_exists_quantitativeHilbertData_via_coordinates (supply : HasQuantitativeHilbertModels) :
    ∃ d : AlmostIsometricFamily, d.HasContractivelyComplementedCopy ∧ d.HasCoordinateSplitting := by
  let s := QuantitativeHilbertSequence.ofModels supply
  exact ⟨s.metricFamily, s.hasContractivelyComplementedCopy_metricFamily, s.hasCoordinateSplitting_metricFamily⟩

end BanachGeometry
