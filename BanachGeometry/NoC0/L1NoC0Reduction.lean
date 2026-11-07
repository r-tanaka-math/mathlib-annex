import BanachGeometry.SequenceSpaces.ScalarBasis
import BanachGeometry.SequenceSpaces.CanonicalSequences
import BanachGeometry.WeakSequences.OperatorTails
import BanachGeometry.OperatorGraphs.GraphObstruction

open scoped ENNReal

/-! R6 Lemma 6.4 from explicit coordinate BasisDecay propositions, using
finite-head estimates and operator tails. BasisDecay is an ordinary premise,
never an instance, axiom or additional field of QuantitativeHilbertData.
NoC0/BasisDecay proves the no-c₀ implication via basisDecay_of_not_containsLinearCopy;
NoC0Closure applies it to the coordinate spaces and finite graph families. -/
noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry

namespace L1NoC0
variable (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]

theorem no_c0_of_basisDecay (hdecay : ∀ j, BasisDecay (V j)) :
    ¬ ContainsLinearCopy ScalarC0 (L1Sum V) := by
  classical
  letI : SeparableSpace (ScalarC0 →L[ℝ] ℝ) := separableSpace_dual_scalarC0
  rintro ⟨T,b,hb,hT⟩
  have htail := L1Tails.tendsto_opNorm_tail_comp V T
  obtain ⟨m,hm⟩ := Filter.eventually_atTop.1
    (htail.eventually (eventually_lt_nhds (by positivity : 0 < b/4)))
  have hfinite (s : Finset ℕ) : Tendsto
      (fun n => ∑ j ∈ s, ‖T (CanonicalSequences.scalarBasis n) j‖) atTop (nhds 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert j s hjs ih =>
      have hj : Tendsto (fun n => ‖T (CanonicalSequences.scalarBasis n) j‖) atTop (nhds 0) :=
        hdecay j ((lp.evalCLM ℝ V 1 j).comp T)
      simpa only [Finset.sum_insert hjs, add_zero] using hj.add ih
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1
    ((hfinite (Finset.range m)).eventually (eventually_lt_nhds (by positivity : 0 < b/4)))
  let x := CanonicalSequences.scalarBasis N
  have hnx : ‖x‖ = 1 := CanonicalSequences.norm_scalarBasis N
  have hhead : ‖L1Tails.head V m (T x)‖ < b/4 := by
    rw [L1Tails.head_eq_sum]
    apply (norm_sum_le _ _).trans_lt
    simpa only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))] using hN N le_rfl
  have ht : ‖L1Tails.tail V m (T x)‖ < b/4 := by
    calc
      _ ≤ ‖(L1Tails.tail V m).comp T‖ * ‖x‖ := ((L1Tails.tail V m).comp T).le_opNorm x
      _ = ‖(L1Tails.tail V m).comp T‖ := by rw [hnx, mul_one]
      _ < b/4 := hm m le_rfl
  have hsplit : T x = L1Tails.head V m (T x) + L1Tails.tail V m (T x) := by
    rw [L1Tails.tail_eq_sub_head]; abel
  have hsmall : ‖T x‖ < b := by
    conv_lhs => rw [hsplit]
    have he := norm_add_le (L1Tails.head V m (T x)) (L1Tails.tail V m (T x))
    linarith
  have hlo := hT x
  rw [hnx, mul_one] at hlo
  exact hsmall.not_ge hlo

end L1NoC0

namespace WeightedGraph
theorem no_c0L2_of_coordinate_basisDecay (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)
    («hλ» : ∀ j, 0 < «λ» j) (hQ : ∀ j, CompletelyContinuous (Q j))
    (hdecay : ∀ j, BasisDecay (A j)) :
    ¬ ContainsLinearCopy C0L2 (Space A B Q «λ») :=
  no_c0L2_of_no_c0_l1 A B Q «λ» «hλ» hQ (L1NoC0.no_c0_of_basisDecay A hdecay)
end WeightedGraph
end BanachGeometry
