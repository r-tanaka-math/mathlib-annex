import BanachGeometry.SequenceSpaces.CanonicalSequences
import BanachGeometry.NoC0.HilbertC0Obstruction
import BanachGeometry.OperatorGraphs.GraphSupport
import BanachGeometry.SequenceSpaces.UnitBall

/-! Heterogeneous graph obstruction with arbitrarily positive weights. Its local
theorem takes no-c₀ of the full ℓ₁ ambient space as an ordinary argument.
NoC0/L1NoC0Reduction and NoC0/NoC0Closure discharge that argument from coordinate
no-c₀ using the proved BP-basis result. No weak sequential completeness is assumed.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace WeightedGraph
variable (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)

theorem no_c0L2_of_no_c0_l1 («hλ» : ∀ j, 0 < «λ» j)
    (hQ : ∀ j, CompletelyContinuous (Q j))
    (hNoL1 : ¬ ContainsLinearCopy ScalarC0 (L1Sum A)) :
    ¬ ContainsLinearCopy C0L2 (Space A B Q «λ») := by
  classical
  rintro ⟨S, b, hb, hS⟩
  let O := (output A B Q «λ»).comp S
  have hnull (n j : ℕ) : Tendsto
      (fun k => (O (CanonicalSequences.column n (CanonicalSequences.l2Basis k))) j)
      atTop (nhds 0) := by
    let U := ((coord A B Q «λ» j).comp S).comp
      (CanonicalSequences.column n).toContinuousLinearMap
    have hweak : WeakNull (fun k => U (CanonicalSequences.l2Basis k)) := by
      intro f
      exact CanonicalSequences.weakNull_l2Basis (f.comp U)
    have ht := hQ j _ hweak
    change Tendsto (fun k => Q j (coord A B Q «λ» j
      (S (CanonicalSequences.column n (CanonicalSequences.l2Basis k))))) atTop (nhds 0) at ht
    simp only [coord_output A B Q «λ» «hλ»] at ht
    exact ht
  let η := fun n => b * ApproximationParameters.weight 0 n
  have hηpos (n : ℕ) : 0 < η n := mul_pos hb (ApproximationParameters.weight_pos 0 n)
  have hsmall (n : ℕ) : ∃ t : ScalarL2, ‖t‖ = 1 ∧ ‖O (CanonicalSequences.column n t)‖ < η n := by
    apply UnitBall.exists_small_unit (O.comp (CanonicalSequences.column n).toContinuousLinearMap) (η n)
    intro hlo
    exact HilbertC0.no_lower_of_coordinate_null B
      (O.comp (CanonicalSequences.column n).toContinuousLinearMap)
      CanonicalSequences.l2Basis CanonicalSequences.orthonormal_l2Basis
      (hnull n) (η n) (hηpos n) hlo
  choose t ht htO using hsmall
  let R := CanonicalSequences.scalarCopy t ht
  have hR (a : ScalarC0) : ‖R a‖ = ‖a‖ := CanonicalSequences.norm_scalarCopy t ht a
  have hsum : Summable η := (ApproximationParameters.weight_summable 0).mul_left b
  have htsum : (∑' n, η n) = b / 2 := by
    rw [tsum_mul_left, ApproximationParameters.weights_sum]
    norm_num [ApproximationParameters.theta, div_eq_mul_inv]
  have hO (a : ScalarC0) : ‖O (R a)‖ ≤ (b / 2) * ‖a‖ := by
    have he := CanonicalSequences.norm_comp_scalarCopy_le O t ht η
      (fun n => (hηpos n).le) hsum (fun n => (htO n).le) a
    simpa only [R, htsum] using he
  let L := (weighted A B Q «λ»).comp (S.comp R)
  apply hNoL1
  refine ⟨L, b, hb, ?_⟩
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hlo := hS (R a)
    rw [hR] at hlo
    change b * ‖a‖ ≤ max ‖L a‖ ‖O (R a)‖ at hlo
    have hout : ‖O (R a)‖ < b * ‖a‖ := (hO a).trans_lt (by nlinarith [mul_pos hb ha'])
    by_contra hbad
    have hlin : ‖L a‖ < b * ‖a‖ := lt_of_not_ge hbad
    exact (max_lt hlin hout).not_ge hlo

end WeightedGraph
end BanachGeometry
