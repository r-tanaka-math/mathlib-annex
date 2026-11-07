import BanachGeometry.NoC0.BasisDecay
import BanachGeometry.OperatorGraphs.FiniteExclusionFromDecay

/-! Hypothesis-closed no-c₀ exports. BP is supplied by the constructed
basisDecay_of_not_containsLinearCopy proof, not by a new assumption.
All dependent coordinates, positive weights, repeats, and q=0 are retained.
W05 Source execution evidence is external. -/
noncomputable section
namespace BanachGeometry
namespace L1NoC0

theorem no_c0_of_coordinate_no_c0 (V : ℕ → Type*)
    [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    (hno : ∀ j, ¬ ContainsLinearCopy ScalarC0 (V j)) :
    ¬ ContainsLinearCopy ScalarC0 (L1Sum V) :=
  no_c0_of_basisDecay V (fun j => basisDecay_of_not_containsLinearCopy (V j) (hno j))

end L1NoC0
namespace WeightedGraph

theorem no_c0L2 (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j)
    (hQ : ∀ j, CompletelyContinuous (Q j))
    (hno : ∀ j, ¬ ContainsLinearCopy ScalarC0 (A j)) :
    ¬ ContainsLinearCopy C0L2 (Space A B Q «λ») :=
  no_c0L2_of_no_c0_l1 A B Q «λ» «hλ» hQ (L1NoC0.no_c0_of_coordinate_no_c0 A hno)

theorem finite_no_c0L2 (q : ℕ) (A B : Fin q → ℕ → Type)
    [∀ r j, NormedAddCommGroup (A r j)] [∀ r j, NormedSpace ℝ (A r j)]
    [∀ r j, NormedAddCommGroup (B r j)] [∀ r j, NormedSpace ℝ (B r j)]
    (Q : ∀ r j, A r j →L[ℝ] B r j) («λ» : Fin q → ℕ → ℝ)
    («hλ» : ∀ r j, 0 < «λ» r j) (hQ : ∀ r j, CompletelyContinuous (Q r j))
    (hno : ∀ r j, ¬ ContainsLinearCopy ScalarC0 (A r j)) :
    ¬ ContainsLinearCopy C0L2 (∀ r, Space (A r) (B r) (Q r) («λ» r)) :=
  finite_no_c0L2_of_basisDecay q A B Q «λ» «hλ» hQ
    (fun r j => basisDecay_of_not_containsLinearCopy (A r j) (hno r j))

end WeightedGraph
namespace QuantitativeHilbertSequence

theorem excludesFiniteSumCopy_metricFamily (s : QuantitativeHilbertSequence) : s.metricFamily.ExcludesFiniteSumCopy :=
  s.excludesFiniteSumCopy_of_basisDecay (fun n => basisDecay_of_not_containsLinearCopy (s.A n).Carrier (s.input n).no_c0)

theorem exists_almostIsometric_nonisomorphic_pair (s : QuantitativeHilbertSequence) : ExistsAlmostIsometricNonisomorphicPair := s.exists_almostIsometric_nonisomorphic_pair_of_finite_exclusion s.excludesFiniteSumCopy_metricFamily

end QuantitativeHilbertSequence

theorem exists_almostIsometric_nonisomorphic_pair_of_exists_quantitativeHilbertData_via_coordinates (supply : HasQuantitativeHilbertModels) : ExistsAlmostIsometricNonisomorphicPair :=
  (QuantitativeHilbertSequence.ofModels supply).exists_almostIsometric_nonisomorphic_pair

end BanachGeometry
