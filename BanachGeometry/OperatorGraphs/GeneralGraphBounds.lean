import BanachGeometry.OperatorGraphs.GeneralGraphChange
import BanachGeometry.AlmostIsometric.OptimalLipschitz

/-! Two-constant graph bounds with arbitrary positive lower/upper constants,
using the coordinate/change construction. No norm-preserving h assumption is retained.
Execution evidence is recorded in the external receipts. -/

noncomputable section
namespace BanachGeometry
namespace GeneralGraphBounds
variable {A H : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (a : QuantitativeGraphData A H) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ»)

abbrev X := GeneralGraphChange.Source a «λ»
abbrev Y := GeneralGraphChange.Target a «λ»
def forwardConstant : ℝ := max (1 + ∑' j, «λ» j) a.upperConstant
def inverseConstant : ℝ := max (1 + 2 * (∑' j, «λ» j) / a.lowerConstant) a.lowerConstant⁻¹

include «hλ»

theorem pair_sub_le (j : ℕ) (x x' : X a «λ») :
    ‖GeneralGraphCoordinate.pair a (WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x)) -
      GeneralGraphCoordinate.pair a (WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x'))‖ ≤ ‖x - x'‖ := by
  rw [← GeneralGraphChange.tilde_eq_pair a j, ← GeneralGraphChange.tilde_eq_pair a j,
    ← map_sub, ← map_sub]
  exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j (x - x')

theorem fcoord_sub_le (j : ℕ) (x x' : X a «λ») :
    ‖GeneralGraphChange.fcoord a «λ» x j - GeneralGraphChange.fcoord a «λ» x' j‖ ≤
      ‖GeneralGraphChange.sourceCoord a «λ» j (x - x')‖ + ‖x - x'‖ := by
  have h := GeneralGraphCoordinate.forward_difference a
    (WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x))
    (WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x'))
  have hfst : ‖(WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x)).1 -
      (WithLp.ofLp (GeneralGraphChange.sourceCoord a «λ» j x')).1‖ ≤
      ‖GeneralGraphChange.sourceCoord a «λ» j (x - x')‖ := by
    rw [map_sub]
    exact WithLp.norm_fst_le A
      (GeneralGraphChange.sourceCoord a «λ» j x - GeneralGraphChange.sourceCoord a «λ» j x')
  exact h.trans (add_le_add hfst (pair_sub_le a «λ» «hλ» j x x'))

theorem inverse_pair_sub_le (hc : 0 < a.lowerConstant) (j : ℕ) (y y' : Y a «λ») :
    ‖a.h.symm (a.linearMap (GeneralGraphChange.targetCoord a «λ» j y)) -
      a.h.symm (a.linearMap (GeneralGraphChange.targetCoord a «λ» j y'))‖ ≤ a.lowerConstant⁻¹ * ‖y - y'‖ := by
  apply (GeneralGraphCoordinate.inverse_pair_difference a hc _ _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
  rw [← map_sub, ← map_sub]
  exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j (y - y')

theorem bcoord_sub_le (hc : 0 < a.lowerConstant) (j : ℕ) (y y' : Y a «λ») :
    ‖GeneralGraphChange.bcoord a «λ» y j - GeneralGraphChange.bcoord a «λ» y' j‖ ≤
      ‖GeneralGraphChange.targetCoord a «λ» j (y - y')‖ + 2 * (a.lowerConstant⁻¹ * ‖y - y'‖) := by
  have h := GeneralGraphCoordinate.backward_difference a
    (GeneralGraphChange.targetCoord a «λ» j y) (GeneralGraphChange.targetCoord a «λ» j y')
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖(GeneralGraphCoordinate.backward a (GeneralGraphChange.targetCoord a «λ» j y)).1 -
      (GeneralGraphCoordinate.backward a (GeneralGraphChange.targetCoord a «λ» j y')).1‖ +
    ‖(GeneralGraphCoordinate.backward a (GeneralGraphChange.targetCoord a «λ» j y)).2 -
      (GeneralGraphCoordinate.backward a (GeneralGraphChange.targetCoord a «λ» j y')).2‖ ≤ _
  rw [map_sub]
  exact h.trans (by linarith [inverse_pair_sub_le a «λ» «hλ» hc j y y'])

theorem forward_sub_le (hc : 0 ≤ a.upperConstant) (x x' : X a «λ») :
    ‖GeneralGraphChange.forward a «λ» «hλ» hsum x - GeneralGraphChange.forward a «λ» «hλ» hsum x'‖ ≤
      forwardConstant a «λ» * ‖x - x'‖ := by
  let z := GeneralGraphChange.forward a «λ» «hλ» hsum x - GeneralGraphChange.forward a «λ» «hλ» hsum x'
  have hz := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» z).1
  have hx := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» (x - x')).1
  apply WeightedGraph.norm_le_of_sum_le_of_images_le _ _ _ _ «hλ» z _
  · have hsumle : (∑' j, «λ» j * ‖GeneralGraphChange.targetCoord a «λ» j z‖) ≤
        (1 + ∑' j, «λ» j) * ‖x - x'‖ := by
      calc
        _ ≤ ∑' j, («λ» j * ‖GeneralGraphChange.sourceCoord a «λ» j (x - x')‖ + «λ» j * ‖x - x'‖) := by
          apply hz.tsum_le_tsum _ (hx.add (hsum.mul_right ‖x - x'‖))
          intro j
          change «λ» j * ‖GeneralGraphChange.targetCoord a «λ» j
            (GeneralGraphChange.forward a «λ» «hλ» hsum x - GeneralGraphChange.forward a «λ» «hλ» hsum x')‖ ≤ _
          rw [map_sub, GeneralGraphChange.coord_forward, GeneralGraphChange.coord_forward]
          exact (mul_le_mul_of_nonneg_left (fcoord_sub_le a «λ» «hλ» j x x') («hλ» j).le).trans_eq (mul_add _ _ _)
        _ = (∑' j, «λ» j * ‖GeneralGraphChange.sourceCoord a «λ» j (x - x')‖) +
            (∑' j, «λ» j) * ‖x - x'‖ := by rw [hx.tsum_add (hsum.mul_right _), tsum_mul_right]
        _ ≤ ‖x - x'‖ + (∑' j, «λ» j) * ‖x - x'‖ :=
          add_le_add (WeightedGraph.sum_weighted_le_norm _ _ _ _ «hλ» (x - x')) le_rfl
        _ = (1 + ∑' j, «λ» j) * ‖x - x'‖ := by ring
    exact hsumle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro j
    change ‖a.linearMap (GeneralGraphChange.targetCoord a «λ» j z)‖ ≤ _
    change ‖a.linearMap (GeneralGraphChange.targetCoord a «λ» j
      (GeneralGraphChange.forward a «λ» «hλ» hsum x - GeneralGraphChange.forward a «λ» «hλ» hsum x'))‖ ≤
      forwardConstant a «λ» * ‖x - x'‖
    rw [map_sub, GeneralGraphChange.coord_forward, GeneralGraphChange.coord_forward, map_sub,
      GeneralGraphChange.fcoord, GeneralGraphChange.fcoord, GeneralGraphCoordinate.map_forward, GeneralGraphCoordinate.map_forward]
    exact (a.upper _ _).trans
      ((mul_le_mul_of_nonneg_left (pair_sub_le a «λ» «hλ» j x x') (by linarith : 0 ≤ a.upperConstant)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

theorem backward_sub_le (hc : 0 < a.lowerConstant) (y y' : Y a «λ») :
    ‖GeneralGraphChange.backward a «λ» «hλ» hsum y - GeneralGraphChange.backward a «λ» «hλ» hsum y'‖ ≤
      inverseConstant a «λ» * ‖y - y'‖ := by
  let z := GeneralGraphChange.backward a «λ» «hλ» hsum y - GeneralGraphChange.backward a «λ» «hλ» hsum y'
  have hz := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» z).1
  have hy := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» (y - y')).1
  apply WeightedGraph.norm_le_of_sum_le_of_images_le _ _ _ _ «hλ» z _
  · have hsumle : (∑' j, «λ» j * ‖GeneralGraphChange.sourceCoord a «λ» j z‖) ≤
        (1 + 2 * (∑' j, «λ» j) / a.lowerConstant) * ‖y - y'‖ := by
      calc
        _ ≤ ∑' j, («λ» j * ‖GeneralGraphChange.targetCoord a «λ» j (y - y')‖ +
            «λ» j * (2 * (a.lowerConstant⁻¹ * ‖y - y'‖))) := by
          apply hz.tsum_le_tsum _ (hy.add (hsum.mul_right _))
          intro j
          change «λ» j * ‖GeneralGraphChange.sourceCoord a «λ» j
            (GeneralGraphChange.backward a «λ» «hλ» hsum y - GeneralGraphChange.backward a «λ» «hλ» hsum y')‖ ≤ _
          rw [map_sub, GeneralGraphChange.coord_backward, GeneralGraphChange.coord_backward]
          exact (mul_le_mul_of_nonneg_left (bcoord_sub_le a «λ» «hλ» hc j y y') («hλ» j).le).trans_eq (mul_add _ _ _)
        _ = (∑' j, «λ» j * ‖GeneralGraphChange.targetCoord a «λ» j (y - y')‖) +
            (∑' j, «λ» j) * (2 * (a.lowerConstant⁻¹ * ‖y - y'‖)) := by
          rw [hy.tsum_add (hsum.mul_right _), tsum_mul_right]
        _ ≤ ‖y - y'‖ + (∑' j, «λ» j) * (2 * (a.lowerConstant⁻¹ * ‖y - y'‖)) :=
          add_le_add (WeightedGraph.sum_weighted_le_norm _ _ _ _ «hλ» (y - y')) le_rfl
        _ = (1 + 2 * (∑' j, «λ» j) / a.lowerConstant) * ‖y - y'‖ := by rw [div_eq_mul_inv]; ring
    exact hsumle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro j
    change ‖GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2
      (fun _ => a.linearMap) j (GeneralGraphChange.sourceCoord a «λ» j z)‖ ≤ _
    change ‖GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2
      (fun _ => a.linearMap) j (GeneralGraphChange.sourceCoord a «λ» j
        (GeneralGraphChange.backward a «λ» «hλ» hsum y - GeneralGraphChange.backward a «λ» «hλ» hsum y'))‖ ≤
      inverseConstant a «λ» * ‖y - y'‖
    rw [map_sub, GeneralGraphChange.coord_backward, GeneralGraphChange.coord_backward, map_sub,
      GeneralGraphChange.tilde_bcoord, GeneralGraphChange.tilde_bcoord]
    exact (inverse_pair_sub_le a «λ» «hλ» hc j y y').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

def pointed (hc : 0 ≤ a.upperConstant) (hlower : 0 < a.lowerConstant) (C : ℝ)
    (hforward : forwardConstant a «λ» ≤ C) (hbackward : inverseConstant a «λ» ≤ C) :
    PointedBiLip (X a «λ») (Y a «λ») C where
  equiv := GeneralGraphChange.equiv a «λ» «hλ» hsum
  zero_eq := GeneralGraphChange.forward_zero a «λ» «hλ» hsum
  forward x x' := (forward_sub_le a «λ» «hλ» hsum hc x x').trans
    (mul_le_mul_of_nonneg_right hforward (norm_nonneg _))
  backward y y' := (backward_sub_le a «λ» «hλ» hsum hlower y y').trans
    (mul_le_mul_of_nonneg_right hbackward (norm_nonneg _))

include hsum in
/-- R6 Proposition 6.8 with two arbitrary positive constants and the
actual whole-space bijection; no norm-preservation assumption on h. -/
theorem exists_quantitative_equiv : ∃ f : X a «λ» ≃ Y a «λ»,
    f 0 = 0 ∧
    (∀ x x', ‖f x-f x'‖ ≤ max (1+∑' j, «λ» j) a.upperConstant * ‖x-x'‖) ∧
    (∀ y y', ‖f.symm y-f.symm y'‖ ≤
      max (1+2*(∑' j, «λ» j)/a.lowerConstant) a.lowerConstant⁻¹ * ‖y-y'‖) := by
  refine ⟨GeneralGraphChange.equiv a «λ» «hλ» hsum,GeneralGraphChange.forward_zero a «λ» «hλ» hsum,?_,?_⟩
  · exact forward_sub_le a «λ» «hλ» hsum a.upper_pos.le
  · exact backward_sub_le a «λ» «hλ» hsum a.lower_pos

theorem optimalConstant_forward_le :
    OptimalLipschitz.finiteConstant (GeneralGraphChange.equiv a «λ» «hλ» hsum : X a «λ» → Y a «λ») ≤
      forwardConstant a «λ» := by
  apply OptimalLipschitz.finiteConstant_le
  refine ⟨a.upper_pos.le.trans (le_max_right _ _),?_⟩
  intro x x'
  simp only [dist_eq_norm]
  change ‖GeneralGraphChange.forward a «λ» «hλ» hsum x - GeneralGraphChange.forward a «λ» «hλ» hsum x'‖ ≤
    forwardConstant a «λ» * ‖x - x'‖
  exact forward_sub_le a «λ» «hλ» hsum a.upper_pos.le x x'

theorem optimalConstant_backward_le :
    OptimalLipschitz.finiteConstant ((GeneralGraphChange.equiv a «λ» «hλ» hsum).symm : Y a «λ» → X a «λ») ≤
      inverseConstant a «λ» := by
  apply OptimalLipschitz.finiteConstant_le
  refine ⟨(inv_nonneg.mpr a.lower_pos.le).trans (le_max_right _ _),?_⟩
  intro y y'
  simp only [dist_eq_norm]
  change ‖GeneralGraphChange.backward a «λ» «hλ» hsum y - GeneralGraphChange.backward a «λ» «hλ» hsum y'‖ ≤
    inverseConstant a «λ» * ‖y - y'‖
  exact backward_sub_le a «λ» «hλ» hsum a.lower_pos y y'

end GeneralGraphBounds
end BanachGeometry
