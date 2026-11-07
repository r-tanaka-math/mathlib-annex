import BanachGeometry.OperatorGraphs.GraphChange
import BanachGeometry.AlmostIsometric.PointedBiLip

/-! The two separate constants of R6 Proposition 6.8 on the original norms:
forward max{1+θ,1+4c}, inverse max{1+2θ/(1−4c),(1−4c)⁻¹}.
No change to an equivalent maximum norm on the source coordinates is used.
Local execution status is recorded in the external qualification receipts. -/

noncomputable section
namespace BanachGeometry
namespace GraphBounds
variable {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ»)

abbrev X := GraphChange.source a «λ»
abbrev Y := GraphChange.target a «λ»
def forwardConstant : ℝ := max (1 + ∑' j, «λ» j) (1 + 4 * c)
def inverseConstant : ℝ := max (1 + 2 * (∑' j, «λ» j) / (1 - 4 * c)) (1 - 4 * c)⁻¹

include «hλ»

theorem pair_sub_le (j : ℕ) (x x' : X a «λ») :
    ‖GraphCoordinate.pair a (WithLp.ofLp (GraphChange.sourceCoord a «λ» j x)) -
      GraphCoordinate.pair a (WithLp.ofLp (GraphChange.sourceCoord a «λ» j x'))‖ ≤ ‖x - x'‖ := by
  rw [← GraphChange.tilde_eq_pair a j, ← GraphChange.tilde_eq_pair a j,
    ← map_sub, ← map_sub]
  exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j (x - x')

theorem fcoord_sub_le (j : ℕ) (x x' : X a «λ») :
    ‖GraphChange.fcoord a «λ» x j - GraphChange.fcoord a «λ» x' j‖ ≤
      ‖GraphChange.sourceCoord a «λ» j (x - x')‖ + ‖x - x'‖ := by
  have h := GraphCoordinate.forward_difference a
    (WithLp.ofLp (GraphChange.sourceCoord a «λ» j x))
    (WithLp.ofLp (GraphChange.sourceCoord a «λ» j x'))
  have hfst : ‖(WithLp.ofLp (GraphChange.sourceCoord a «λ» j x)).1 -
      (WithLp.ofLp (GraphChange.sourceCoord a «λ» j x')).1‖ ≤
      ‖GraphChange.sourceCoord a «λ» j (x - x')‖ := by
    rw [map_sub]
    exact WithLp.norm_fst_le A.Carrier
      (GraphChange.sourceCoord a «λ» j x - GraphChange.sourceCoord a «λ» j x')
  exact h.trans (add_le_add hfst (pair_sub_le a «λ» «hλ» j x x'))

theorem inverse_pair_sub_le (hc : 0 < 1 - 4 * c) (j : ℕ) (y y' : Y a «λ») :
    ‖a.h.symm (a.linearMap (GraphChange.targetCoord a «λ» j y)) -
      a.h.symm (a.linearMap (GraphChange.targetCoord a «λ» j y'))‖ ≤ (1 - 4 * c)⁻¹ * ‖y - y'‖ := by
  apply (GraphCoordinate.inverse_pair_difference a hc _ _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
  rw [← map_sub, ← map_sub]
  exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j (y - y')

theorem bcoord_sub_le (hc : 0 < 1 - 4 * c) (j : ℕ) (y y' : Y a «λ») :
    ‖GraphChange.bcoord a «λ» y j - GraphChange.bcoord a «λ» y' j‖ ≤
      ‖GraphChange.targetCoord a «λ» j (y - y')‖ + 2 * ((1 - 4 * c)⁻¹ * ‖y - y'‖) := by
  have h := GraphCoordinate.backward_difference a
    (GraphChange.targetCoord a «λ» j y) (GraphChange.targetCoord a «λ» j y')
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖(GraphCoordinate.backward a (GraphChange.targetCoord a «λ» j y)).1 -
      (GraphCoordinate.backward a (GraphChange.targetCoord a «λ» j y')).1‖ +
    ‖(GraphCoordinate.backward a (GraphChange.targetCoord a «λ» j y)).2 -
      (GraphCoordinate.backward a (GraphChange.targetCoord a «λ» j y')).2‖ ≤ _
  rw [map_sub]
  exact h.trans (by linarith [inverse_pair_sub_le a «λ» «hλ» hc j y y'])

theorem forward_sub_le (hc : 0 ≤ c) (x x' : X a «λ») :
    ‖GraphChange.forward a «λ» «hλ» hsum x - GraphChange.forward a «λ» «hλ» hsum x'‖ ≤
      forwardConstant (c := c) «λ» * ‖x - x'‖ := by
  let z := GraphChange.forward a «λ» «hλ» hsum x - GraphChange.forward a «λ» «hλ» hsum x'
  have hz := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» z).1
  have hx := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» (x - x')).1
  apply WeightedGraph.norm_le_of_sum_le_of_images_le _ _ _ _ «hλ» z _
  · have hsumle : (∑' j, «λ» j * ‖GraphChange.targetCoord a «λ» j z‖) ≤
        (1 + ∑' j, «λ» j) * ‖x - x'‖ := by
      calc
        _ ≤ ∑' j, («λ» j * ‖GraphChange.sourceCoord a «λ» j (x - x')‖ + «λ» j * ‖x - x'‖) := by
          apply hz.tsum_le_tsum _ (hx.add (hsum.mul_right ‖x - x'‖))
          intro j
          change «λ» j * ‖GraphChange.targetCoord a «λ» j
            (GraphChange.forward a «λ» «hλ» hsum x - GraphChange.forward a «λ» «hλ» hsum x')‖ ≤ _
          rw [map_sub, GraphChange.coord_forward, GraphChange.coord_forward]
          exact (mul_le_mul_of_nonneg_left (fcoord_sub_le a «λ» «hλ» j x x') («hλ» j).le).trans_eq (mul_add _ _ _)
        _ = (∑' j, «λ» j * ‖GraphChange.sourceCoord a «λ» j (x - x')‖) +
            (∑' j, «λ» j) * ‖x - x'‖ := by rw [hx.tsum_add (hsum.mul_right _), tsum_mul_right]
        _ ≤ ‖x - x'‖ + (∑' j, «λ» j) * ‖x - x'‖ :=
          add_le_add (WeightedGraph.sum_weighted_le_norm _ _ _ _ «hλ» (x - x')) le_rfl
        _ = (1 + ∑' j, «λ» j) * ‖x - x'‖ := by ring
    exact hsumle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro j
    change ‖a.linearMap (GraphChange.targetCoord a «λ» j z)‖ ≤ _
    change ‖a.linearMap (GraphChange.targetCoord a «λ» j
      (GraphChange.forward a «λ» «hλ» hsum x - GraphChange.forward a «λ» «hλ» hsum x'))‖ ≤
      forwardConstant (c := c) «λ» * ‖x - x'‖
    rw [map_sub, GraphChange.coord_forward, GraphChange.coord_forward, map_sub,
      GraphChange.fcoord, GraphChange.fcoord, GraphCoordinate.linearMap_forward, GraphCoordinate.linearMap_forward]
    exact (a.upper _ _).trans
      ((mul_le_mul_of_nonneg_left (pair_sub_le a «λ» «hλ» j x x') (by linarith : 0 ≤ 1 + 4 * c)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

theorem backward_sub_le (hc : 0 < 1 - 4 * c) (y y' : Y a «λ») :
    ‖GraphChange.backward a «λ» «hλ» hsum y - GraphChange.backward a «λ» «hλ» hsum y'‖ ≤
      inverseConstant (c := c) «λ» * ‖y - y'‖ := by
  let z := GraphChange.backward a «λ» «hλ» hsum y - GraphChange.backward a «λ» «hλ» hsum y'
  have hz := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» z).1
  have hy := (WeightedGraph.coordinates_admissible _ _ _ _ «hλ» (y - y')).1
  apply WeightedGraph.norm_le_of_sum_le_of_images_le _ _ _ _ «hλ» z _
  · have hsumle : (∑' j, «λ» j * ‖GraphChange.sourceCoord a «λ» j z‖) ≤
        (1 + 2 * (∑' j, «λ» j) / (1 - 4 * c)) * ‖y - y'‖ := by
      calc
        _ ≤ ∑' j, («λ» j * ‖GraphChange.targetCoord a «λ» j (y - y')‖ +
            «λ» j * (2 * ((1 - 4 * c)⁻¹ * ‖y - y'‖))) := by
          apply hz.tsum_le_tsum _ (hy.add (hsum.mul_right _))
          intro j
          change «λ» j * ‖GraphChange.sourceCoord a «λ» j
            (GraphChange.backward a «λ» «hλ» hsum y - GraphChange.backward a «λ» «hλ» hsum y')‖ ≤ _
          rw [map_sub, GraphChange.coord_backward, GraphChange.coord_backward]
          exact (mul_le_mul_of_nonneg_left (bcoord_sub_le a «λ» «hλ» hc j y y') («hλ» j).le).trans_eq (mul_add _ _ _)
        _ = (∑' j, «λ» j * ‖GraphChange.targetCoord a «λ» j (y - y')‖) +
            (∑' j, «λ» j) * (2 * ((1 - 4 * c)⁻¹ * ‖y - y'‖)) := by
          rw [hy.tsum_add (hsum.mul_right _), tsum_mul_right]
        _ ≤ ‖y - y'‖ + (∑' j, «λ» j) * (2 * ((1 - 4 * c)⁻¹ * ‖y - y'‖)) :=
          add_le_add (WeightedGraph.sum_weighted_le_norm _ _ _ _ «hλ» (y - y')) le_rfl
        _ = (1 + 2 * (∑' j, «λ» j) / (1 - 4 * c)) * ‖y - y'‖ := by rw [div_eq_mul_inv]; ring
    exact hsumle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro j
    change ‖GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2
      (fun _ => a.linearMap) j (GraphChange.sourceCoord a «λ» j z)‖ ≤ _
    change ‖GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2
      (fun _ => a.linearMap) j (GraphChange.sourceCoord a «λ» j
        (GraphChange.backward a «λ» «hλ» hsum y - GraphChange.backward a «λ» «hλ» hsum y'))‖ ≤
      inverseConstant (c := c) «λ» * ‖y - y'‖
    rw [map_sub, GraphChange.coord_backward, GraphChange.coord_backward, map_sub,
      GraphChange.tilde_bcoord, GraphChange.tilde_bcoord]
    exact (inverse_pair_sub_le a «λ» «hλ» hc j y y').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

def pointed (hc : 0 ≤ c) (hlower : 0 < 1 - 4 * c) (C : ℝ)
    (hforward : forwardConstant (c := c) «λ» ≤ C) (hbackward : inverseConstant (c := c) «λ» ≤ C) :
    PointedBiLip (X a «λ») (Y a «λ») C where
  equiv := GraphChange.equiv a «λ» «hλ» hsum
  zero_eq := GraphChange.forward_zero a «λ» «hλ» hsum
  forward x x' := (forward_sub_le a «λ» «hλ» hsum hc x x').trans
    (mul_le_mul_of_nonneg_right hforward (norm_nonneg _))
  backward y y' := (backward_sub_le a «λ» «hλ» hsum hlower y y').trans
    (mul_le_mul_of_nonneg_right hbackward (norm_nonneg _))

end GraphBounds
end BanachGeometry
