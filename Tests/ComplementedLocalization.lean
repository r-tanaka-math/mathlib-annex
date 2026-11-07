import BanachGeometry

/- Local execution status is recorded in the external qualification receipts. -/
noncomputable section
open BanachGeometry

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (T : C0Sum V →L[ℝ] L1Shifts.F E) : Localization.JointCorner E V T :=
  Corner.jointCorner E V T

example (supply : HasQuantitativeHilbertModels) : ∃ d : AlmostIsometricFamily, d.HasContractivelyComplementedCopy ∧ d.HasCoordinateSplitting :=
  metricFamily_complemented_splitting_of_exists_quantitativeHilbertData_via_coordinates supply

example {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (hs : Summable «λ»)
    (x : GraphChange.source a «λ») :
    GraphChange.backward a «λ» «hλ» hs (GraphChange.forward a «λ» «hλ» hs x) = x :=
  GraphChange.backward_forward a «λ» «hλ» hs x

#print axioms C0Sum.weakNull_of_coordinateDisjoint
#print axioms Corner.jointCorner
#print axioms Corner.finite_head_localization
#print axioms GraphSplitting.equiv
#print axioms OperatorGraphPair.isometric_complemented
#print axioms GraphChange.equiv
#print axioms GraphBounds.forward_sub_le
#print axioms GraphBounds.backward_sub_le
#print axioms metricFamily_complemented_splitting_of_exists_quantitativeHilbertData_via_coordinates
