import BanachGeometry

/-! Direct consumers of the graph obstruction statements and their explicit inputs.
Actual elaboration and axiom inspection are recorded in the external receipts.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open BanachGeometry

example : TopologicalSpace.SeparableSpace (C0L2 →L[ℝ] ℝ) := separableSpace_dual_c0L2
example : TopologicalSpace.SeparableSpace (ScalarC0 →L[ℝ] ℝ) := separableSpace_dual_scalarC0
example (n : ℕ) : TopologicalSpace.SeparableSpace ((Fin n → C0L2) →L[ℝ] ℝ) :=
  separableSpace_dual_pi_c0L2 n

example (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) : ExistsAlmostIsometricNonisomorphicPair :=
  d.exists_almostIsometric_nonisomorphic_pair_of_complemented_splitting_exclusion h2 h3 h4

example (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) :
    LipschitzDistance.finiteDistance d.FixedX d.FixedY = 1 ∧
      1 ∉ LipschitzDistance.distortions d.FixedX d.FixedY :=
  d.finiteDistance_one_nonattained h2 h3 h4

example (s : QuantitativeHilbertSequence) (h : ∀ n, BasisDecay (s.A n).Carrier) : ExistsAlmostIsometricNonisomorphicPair :=
  s.exists_almostIsometric_nonisomorphic_pair_of_basisDecay h

example (supply : HasQuantitativeHilbertModels)
    (hBP : ∀ E : SeparableRealBanach,
      ¬ ContainsLinearCopy ScalarC0 E.Carrier → BasisDecay E.Carrier) : ExistsAlmostIsometricNonisomorphicPair :=
  exists_almostIsometric_nonisomorphic_pair_of_exists_quantitativeHilbertData_via_coordinates_and_basisDecay supply hBP

example : WeakNull CanonicalSequences.scalarBasis := BasisSeries.weakNull_scalarBasis

#print axioms C0Dual.equiv
#print axioms separableSpace_dual_c0L2
#print axioms HilbertC0.no_lower_of_coordinate_null
#print axioms L1NoC0.no_c0_of_basisDecay
#print axioms WeightedGraph.no_c0L2_of_no_c0_l1
#print axioms FiniteGraph.equiv
#print axioms WeightedGraph.finite_no_c0L2_of_basisDecay
#print axioms HeadSplitting.no_complemented_finiteHead
#print axioms AlmostIsometricFamily.exists_almostIsometric_nonisomorphic_pair_of_complemented_splitting_exclusion
#print axioms AlmostIsometricFamily.finiteDistance_one_nonattained
#print axioms AlmostIsometricFamily.insertion_images_no_cauchy_subsequence
#print axioms QuantitativeHilbertSequence.excludesFiniteSumCopy_of_basisDecay
#print axioms exists_almostIsometric_nonisomorphic_pair_of_exists_quantitativeHilbertData_via_coordinates_and_basisDecay
