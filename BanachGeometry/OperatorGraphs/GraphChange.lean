import BanachGeometry.OperatorGraphs.QuantitativePair
import BanachGeometry.OperatorGraphs.GraphCoordinateEquiv

/-! The countable triangular map and its inverse belong to the stated graph spaces.
Both inverse laws are proved on the retained carriers. Quantitative constants are
proved separately in OperatorGraphs/GraphBounds.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace GraphChange
variable {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) («λ» : ℕ → ℝ)

abbrev source := OperatorGraphPair.X a «λ»
abbrev target := OperatorGraphPair.Y a «λ»
abbrev sourceCoord (j : ℕ) := WeightedGraph.coord _ _
  (GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2 (fun _ => a.linearMap)) «λ» j
abbrev targetCoord (j : ℕ) := WeightedGraph.coord (fun _ : ℕ => A.Carrier)
  (fun _ : ℕ => H.Carrier) (fun _ => a.linearMap) «λ» j

theorem norm_d (z : HilbertPair H.Carrier) : ‖a.d z‖ = ‖z‖ := by
  simpa only [a.d_zero, sub_zero] using GraphCoordinate.d_difference_norm a z 0

theorem tilde_eq_pair (j : ℕ) (z : WithLp 1 (A.Carrier × ScalarL2)) :
    GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2
      (fun _ => a.linearMap) j z = GraphCoordinate.pair a (WithLp.ofLp z) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact GraphSplitting.first_tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier)
      ScalarL2 (fun _ => a.linearMap) j z
  · exact GraphSplitting.second_tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier)
      ScalarL2 (fun _ => a.linearMap) j z

def fcoord (x : source a «λ») (j : ℕ) : A.Carrier :=
  GraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j x))

def bcoord (y : target a «λ») (j : ℕ) : WithLp 1 (A.Carrier × ScalarL2) :=
  WithLp.toLp 1 (GraphCoordinate.backward a (targetCoord a «λ» j y))

theorem norm_bcoord_le (y : target a «λ») (j : ℕ) :
    ‖bcoord a «λ» y j‖ ≤ ‖targetCoord a «λ» j y‖ + 2 * ‖a.linearMap (targetCoord a «λ» j y)‖ := by
  let ν := targetCoord a «λ» j y
  let w := a.h.symm (a.linearMap ν)
  have hw : ‖w‖ = ‖a.linearMap ν‖ := by
    have he := a.h_norm w
    simpa only [w, a.h.apply_symm_apply] using he.symm
  have hs : ‖(WithLp.ofLp w).2‖ ≤ ‖w‖ := WithLp.norm_snd_le H.Carrier w
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖ν - a.d w‖ + ‖(WithLp.ofLp w).2‖ ≤ ‖ν‖ + 2 * ‖a.linearMap ν‖
  have hf := norm_sub_le ν (a.d w)
  rw [norm_d] at hf
  linarith

theorem tilde_bcoord (y : target a «λ») (j : ℕ) :
    GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2
      (fun _ => a.linearMap) j (bcoord a «λ» y j) = a.h.symm (a.linearMap (targetCoord a «λ» j y)) := by
  rw [tilde_eq_pair]
  exact GraphCoordinate.pair_backward a _

variable («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ»)
include «hλ» hsum

theorem forward_admissible (x : source a «λ») :
    WeightedGraph.Admissible (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier)
      (fun _ => a.linearMap) «λ» (fcoord a «λ» x) := by
  have hx := WeightedGraph.coordinates_admissible _ _ _ _ «hλ» x
  constructor
  · apply Summable.of_nonneg_of_le (fun j => mul_nonneg («hλ» j).le (norm_nonneg _))
    · intro j
      have hp : ‖GraphCoordinate.pair a (WithLp.ofLp (sourceCoord a «λ» j x))‖ ≤ ‖x‖ := by
        rw [← tilde_eq_pair a j]
        exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j x
      have hm : ‖(WithLp.ofLp (sourceCoord a «λ» j x)).1‖ ≤ ‖sourceCoord a «λ» j x‖ :=
        WithLp.norm_fst_le A.Carrier (sourceCoord a «λ» j x)
      have hf : ‖fcoord a «λ» x j‖ ≤ ‖sourceCoord a «λ» j x‖ + ‖x‖ := by
        change ‖(WithLp.ofLp (sourceCoord a «λ» j x)).1 +
          a.d (GraphCoordinate.pair a (WithLp.ofLp (sourceCoord a «λ» j x)))‖ ≤ _
        exact (norm_add_le _ _).trans (by rw [norm_d]; exact add_le_add hm hp)
      calc
        «λ» j * ‖fcoord a «λ» x j‖ ≤ «λ» j * (‖sourceCoord a «λ» j x‖ + ‖x‖) :=
          mul_le_mul_of_nonneg_left hf («hλ» j).le
        _ = «λ» j * ‖sourceCoord a «λ» j x‖ + «λ» j * ‖x‖ := mul_add _ _ _
    · exact hx.1.add (hsum.mul_right ‖x‖)
  · have ht := hx.2
    change Tendsto (fun j => ‖GraphSplitting.tilde (fun _ : ℕ => A.Carrier)
      (fun _ : ℕ => H.Carrier) ScalarL2 (fun _ => a.linearMap) j (sourceCoord a «λ» j x)‖)
      atTop (nhds 0) at ht
    simp only [tilde_eq_pair a] at ht
    have he (j : ℕ) : ‖a.linearMap (fcoord a «λ» x j)‖ =
        ‖GraphCoordinate.pair a (WithLp.ofLp (sourceCoord a «λ» j x))‖ := by
      change ‖a.linearMap (GraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j x)))‖ = _
      rw [GraphCoordinate.linearMap_forward, a.h_norm]
    simpa only [he] using ht

theorem backward_admissible (y : target a «λ») :
    WeightedGraph.Admissible (GraphSplitting.Domain (fun _ : ℕ => A.Carrier) ScalarL2)
      (GraphSplitting.Codomain (fun _ : ℕ => H.Carrier) ScalarL2)
      (GraphSplitting.tilde (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2 (fun _ => a.linearMap))
      «λ» (bcoord a «λ» y) := by
  have hy := WeightedGraph.coordinates_admissible _ _ _ _ «hλ» y
  constructor
  · apply Summable.of_nonneg_of_le (fun j => mul_nonneg («hλ» j).le (norm_nonneg _))
    · intro j
      have hQ : ‖a.linearMap (targetCoord a «λ» j y)‖ ≤ ‖y‖ :=
        WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j y
      have hb : ‖bcoord a «λ» y j‖ ≤ ‖targetCoord a «λ» j y‖ + 2 * ‖y‖ :=
        (norm_bcoord_le a «λ» y j).trans (by linarith)
      calc
        «λ» j * ‖bcoord a «λ» y j‖ ≤ «λ» j * (‖targetCoord a «λ» j y‖ + 2 * ‖y‖) :=
          mul_le_mul_of_nonneg_left hb («hλ» j).le
        _ = «λ» j * ‖targetCoord a «λ» j y‖ + «λ» j * (2 * ‖y‖) := mul_add _ _ _
    · exact hy.1.add (hsum.mul_right (2 * ‖y‖))
  · have hw (j : ℕ) : ‖a.h.symm (a.linearMap (targetCoord a «λ» j y))‖ = ‖a.linearMap (targetCoord a «λ» j y)‖ := by
      have h := a.h_norm (a.h.symm (a.linearMap (targetCoord a «λ» j y)))
      simpa only [a.h.apply_symm_apply] using h.symm
    simpa only [tilde_bcoord, hw] using hy.2

def forward (x : source a «λ») : target a «λ» :=
  WeightedGraph.ofCoordinates _ _ _ «λ» «hλ» (fcoord a «λ» x) (forward_admissible a «λ» «hλ» hsum x)

def backward (y : target a «λ») : source a «λ» :=
  WeightedGraph.ofCoordinates _ _ _ «λ» «hλ» (bcoord a «λ» y) (backward_admissible a «λ» «hλ» hsum y)

@[simp] theorem coord_forward (j : ℕ) (x : source a «λ») :
    targetCoord a «λ» j (forward a «λ» «hλ» hsum x) = fcoord a «λ» x j :=
  WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ» _ _ j

@[simp] theorem coord_backward (j : ℕ) (y : target a «λ») :
    sourceCoord a «λ» j (backward a «λ» «hλ» hsum y) = bcoord a «λ» y j :=
  WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ» _ _ j

theorem backward_forward (x : source a «λ») : backward a «λ» «hλ» hsum (forward a «λ» «hλ» hsum x) = x := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_backward]
  change WithLp.toLp 1 (GraphCoordinate.backward a (targetCoord a «λ» j (forward a «λ» «hλ» hsum x))) = _
  rw [coord_forward]
  change WithLp.toLp 1 (GraphCoordinate.backward a
    (GraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j x)))) = _
  rw [GraphCoordinate.backward_forward, WithLp.toLp_ofLp]

theorem forward_backward (y : target a «λ») : forward a «λ» «hλ» hsum (backward a «λ» «hλ» hsum y) = y := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_forward]
  change GraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j (backward a «λ» «hλ» hsum y))) = _
  rw [coord_backward]
  change GraphCoordinate.forward a (GraphCoordinate.backward a (targetCoord a «λ» j y)) = _
  exact GraphCoordinate.forward_backward a _

def equiv : source a «λ» ≃ target a «λ» where
  toFun := forward a «λ» «hλ» hsum
  invFun := backward a «λ» «hλ» hsum
  left_inv := backward_forward a «λ» «hλ» hsum
  right_inv := forward_backward a «λ» «hλ» hsum

theorem forward_zero : forward a «λ» «hλ» hsum 0 = 0 := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_forward, map_zero]
  change GraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j 0)) = 0
  rw [map_zero]
  exact GraphCoordinate.forward_zero a

end GraphChange
end BanachGeometry
