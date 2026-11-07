import BanachGeometry.WeakSequences.C0DualIsometry
import BanachGeometry

/- Local execution status is recorded in the external qualification receipts.
API, elaboration and kernel/axiom evidence are recorded externally. -/
noncomputable section
open BanachGeometry Filter

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ¬ ContainsLinearCopy ScalarC0 E) : BasisDecay E :=
  basisDecay_of_not_containsLinearCopy E h

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    (h : ∀ j, ¬ ContainsLinearCopy ScalarC0 (V j)) : ¬ ContainsLinearCopy ScalarC0 (L1Sum V) :=
  L1NoC0.no_c0_of_coordinate_no_c0 V h

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (x : WeightedL1.Space V «λ») :
    ‖x‖ = ∑' j, «λ» j * ‖WeightedL1.coord V «λ» x j‖ := WeightedL1.norm_eq_tsum_weight_mul_norm_coord V «λ» «hλ» x

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) (h : ∀ j, ¬ ContainsLinearCopy ScalarC0 (V j)) :
    ¬ ContainsLinearCopy ScalarC0 (WeightedL1.Space V «λ») := WeightedL1.no_c0 V «λ» h

example (supply : HasQuantitativeHilbertModels) : ExistsAlmostIsometricNonisomorphicPair := exists_almostIsometric_nonisomorphic_pair_of_exists_quantitativeHilbertData_via_coordinates supply
example : ExistsAlmostIsometricNonisomorphicPair := AlmostIsometricPair.exists_almostIsometric_nonisomorphic_pair

example : LipschitzDistance.finiteOptimalDistance AlmostIsometricPair.xSpace.Carrier AlmostIsometricPair.ySpace.Carrier = 1 :=
  AlmostIsometricPair.finiteOptimalDistance_eq_one

example : 1 ∉ LipschitzDistance.optimalDistortions AlmostIsometricPair.xSpace.Carrier AlmostIsometricPair.ySpace.Carrier :=
  AlmostIsometricPair.optimal_distortion_one_not_attained

example : ContainsComplementedCopy L1C0L2 AlmostIsometricPair.xSpace.Carrier ∧
    ¬ ContainsComplementedCopy L1C0L2 AlmostIsometricPair.ySpace.Carrier :=
  ⟨AlmostIsometricPair.complemented_in_xSpace,AlmostIsometricPair.not_complemented_in_ySpace⟩

example (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AlmostIsometricPair.xSpace.Carrier ≃ AlmostIsometricPair.ySpace.Carrier,
      f 0 = 0 ∧ (∀ x x', ‖f x-f x'‖ ≤ (1+ε)*‖x-x'‖) ∧
      (∀ y y', ‖f.symm y-f.symm y'‖ ≤ (1+ε)*‖y-y'‖) :=
  AlmostIsometricPair.exists_pointed_equiv ε hε

example {A H : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : QuantitativeGraphData A H) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (hs : Summable «λ») :
    ∃ f : GeneralGraphBounds.X d «λ» ≃ GeneralGraphBounds.Y d «λ»,
      f 0 = 0 ∧
      (∀ x x', ‖f x-f x'‖ ≤ max (1+∑' j, «λ» j) d.upperConstant * ‖x-x'‖) ∧
      (∀ y y', ‖f.symm y-f.symm y'‖ ≤
        max (1+2*(∑' j, «λ» j)/d.lowerConstant) d.lowerConstant⁻¹ * ‖y-y'‖) :=
  GeneralGraphBounds.exists_quantitative_equiv d «λ» «hλ» hs

example (h : ∀ η : ℝ, 0 < η → Nonempty (AlmostIsometricGraphPairs.GraphPair (1+η))) : ExistsAlmostIsometricNonisomorphicPair :=
  AlmostIsometricGraphPairs.exists_almostIsometric_nonisomorphic_pair_of_arbitrarily_accurate_graph_pairs h

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    (u : ℕ → L1Sum V) (hu : WeaklyCauchy u) :
    Tendsto (fun m => ⨆ n, ‖L1Tails.tail V m (u n)‖) atTop (nhds 0) :=
  WeakTailGliding.tendsto_iSup_norm_tail_of_weaklyCauchy V u hu

#check C0Dual.linearIsometryEquiv
#check LipschitzFreeProperties.existsUnique_linearization
#check LipschitzFreeProperties.exists_compact_approximation_with_iSup_norm
#check LipschitzFreeProperties.hilbert_free_no_c0
#check LipschitzFreeProperties.optimalConstant_eq_norm_linearize
#check LipschitzFreeLocalization.completelyContinuous_linearize_of_incrementLocality
#check Corner.finite_pi_localization
#check FiniteGraph.canonicalEquiv
#check WeightedGraph.finite_no_c0L2
#check AlmostIsometricFamily.fixed_pair_geometry
#check AlmostIsometricPair.exists_separated_insertion_images
