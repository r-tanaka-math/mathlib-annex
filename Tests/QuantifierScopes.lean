import BanachGeometry.NoC0.BPC0Insertion
import BanachGeometry.SequenceSpaces.WeightedL1
import BanachGeometry.OperatorGraphs.GeneralGraphBounds

/-! Direct consumers preserve the explicit section hypotheses in theorem signatures.
This module is not a production import.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open BanachGeometry
open scoped BigOperators

example (s : ℕ → ℕ) (hs : Function.Injective s) (a : ScalarC0) (j : ℕ) :
    BP.insertValue s a (s j) = a j := BP.insertValue_apply_image s hs a j

example (s : ℕ → ℕ) (hs : Function.Injective s) (a : ScalarC0) :
    ‖BP.rawInsert s a‖ = ‖a‖ := BP.norm_rawInsert s hs a

example (s : ℕ → ℕ) (hs : Function.Injective s) (a : ScalarC0) (j : ℕ) :
    BP.insertCLM s a (s j) = a j := BP.insertCLM_apply_image s hs a j

example (s : ℕ → ℕ) (hs : Function.Injective s) (a : ScalarC0) :
    ‖BP.insertCLM s a‖ = ‖a‖ := BP.norm_insertCLM s hs a

example (s : ℕ → ℕ) (hs : Function.Injective s) (j : ℕ) :
    BP.insertCLM s (CanonicalSequences.scalarBasis j) = CanonicalSequences.scalarBasis (s j) :=
  BP.insertCLM_scalarBasis s hs j

example (s : ℕ → ℕ) (hs : Function.Injective s) (a : ScalarC0) (N : ℕ) :
    BP.insertCLM s (CanonicalSequences.scalarHead N a) =
      ∑ j ∈ Finset.range N, a j • CanonicalSequences.scalarBasis (s j) :=
  BP.insertCLM_scalarHead s hs N a

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (x : WeightedL1.Space V «λ») (j : ℕ) :
    «λ» j * ‖WeightedL1.coord V «λ» x j‖ = ‖x j‖ := WeightedL1.mul_norm_coord V «λ» «hλ» x j

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (x : WeightedL1.Space V «λ») :
    ‖x‖ = ∑' j, «λ» j * ‖WeightedL1.coord V «λ» x j‖ :=
  WeightedL1.norm_eq_tsum_weight_mul_norm_coord V «λ» «hλ» x

example (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (x : WeightedL1.Space V «λ») :
    Summable (fun j => «λ» j * ‖WeightedL1.coord V «λ» x j‖) :=
  WeightedL1.coordinates_summable V «λ» «hλ» x

example {A H : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (d : QuantitativeGraphData A H)
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ») :
    ∃ f : GeneralGraphBounds.X d «λ» ≃ GeneralGraphBounds.Y d «λ»,
      f 0 = 0 ∧
      (∀ x x', ‖f x-f x'‖ ≤ max (1+∑' j, «λ» j) d.upperConstant * ‖x-x'‖) ∧
      (∀ y y', ‖f.symm y-f.symm y'‖ ≤
        max (1+2*(∑' j, «λ» j)/d.lowerConstant) d.lowerConstant⁻¹ * ‖y-y'‖) :=
  GeneralGraphBounds.exists_quantitative_equiv d «λ» «hλ» hsum
