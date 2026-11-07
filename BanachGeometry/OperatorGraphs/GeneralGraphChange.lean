import BanachGeometry.OperatorGraphs.GeneralGraphCoordinate

/-! Two-constant graph change with arbitrary positive lower/upper constants,
using the retained coordinate carriers. No norm-preserving h assumption is retained.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace GeneralGraphChange
variable {A H : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (a : QuantitativeGraphData A H) («λ» : ℕ → ℝ)

abbrev Source := GraphSplitting.X (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap) «λ»
abbrev Target := WeightedGraph.Space (fun _ : ℕ => A) (fun _ : ℕ => H) (fun _ => a.linearMap) «λ»
abbrev sourceCoord (j : ℕ) := WeightedGraph.coord _ _
  (GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap)) «λ» j
abbrev targetCoord (j : ℕ) := WeightedGraph.coord (fun _ : ℕ => A)
  (fun _ : ℕ => H) (fun _ => a.linearMap) «λ» j

theorem norm_d (z : HilbertPair H) : ‖a.d z‖ = ‖z‖ := by
  simpa only [a.d_zero, sub_zero] using GeneralGraphCoordinate.norm_d_sub_d a z 0

theorem tilde_eq_pair (j : ℕ) (z : WithLp 1 (A × ScalarL2)) :
    GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2
      (fun _ => a.linearMap) j z = GeneralGraphCoordinate.pair a (WithLp.ofLp z) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact GraphSplitting.first_tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap) j z
  · exact GraphSplitting.second_tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap) j z

def fcoord (x : Source a «λ») (j : ℕ) : A :=
  GeneralGraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j x))

def bcoord (y : Target a «λ») (j : ℕ) : WithLp 1 (A × ScalarL2) :=
  WithLp.toLp 1 (GeneralGraphCoordinate.backward a (targetCoord a «λ» j y))

theorem norm_bcoord_le (y : Target a «λ») (j : ℕ) :
    ‖bcoord a «λ» y j‖ ≤ ‖targetCoord a «λ» j y‖ + 2 * (a.lowerConstant⁻¹ * ‖a.linearMap (targetCoord a «λ» j y)‖) := by
  let ν := targetCoord a «λ» j y
  let w := a.h.symm (a.linearMap ν)
  have hw : ‖w‖ ≤ a.lowerConstant⁻¹ * ‖a.linearMap ν‖ := a.norm_h_symm_le _
  have hs : ‖(WithLp.ofLp w).2‖ ≤ ‖w‖ := WithLp.norm_snd_le H w
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖ν - a.d w‖ + ‖(WithLp.ofLp w).2‖ ≤ ‖ν‖ + 2 * (a.lowerConstant⁻¹ * ‖a.linearMap ν‖)
  have hf := norm_sub_le ν (a.d w)
  rw [norm_d] at hf
  linarith

theorem tilde_bcoord (y : Target a «λ») (j : ℕ) :
    GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2
      (fun _ => a.linearMap) j (bcoord a «λ» y j) = a.h.symm (a.linearMap (targetCoord a «λ» j y)) := by
  rw [tilde_eq_pair]
  exact GeneralGraphCoordinate.pair_backward a _

variable («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ»)
include «hλ» hsum

theorem forward_admissible (x : Source a «λ») :
    WeightedGraph.Admissible (fun _ : ℕ => A) (fun _ : ℕ => H)
      (fun _ => a.linearMap) «λ» (fcoord a «λ» x) := by
  have hx := WeightedGraph.coordinates_admissible _ _ _ _ «hλ» x
  constructor
  · apply Summable.of_nonneg_of_le (fun j => mul_nonneg («hλ» j).le (norm_nonneg _))
    · intro j
      have hp : ‖GeneralGraphCoordinate.pair a (WithLp.ofLp (sourceCoord a «λ» j x))‖ ≤ ‖x‖ := by
        rw [← tilde_eq_pair a j]
        exact WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j x
      have hm : ‖(WithLp.ofLp (sourceCoord a «λ» j x)).1‖ ≤ ‖sourceCoord a «λ» j x‖ :=
        WithLp.norm_fst_le A (sourceCoord a «λ» j x)
      have hf : ‖fcoord a «λ» x j‖ ≤ ‖sourceCoord a «λ» j x‖ + ‖x‖ := by
        change ‖(WithLp.ofLp (sourceCoord a «λ» j x)).1 +
          a.d (GeneralGraphCoordinate.pair a (WithLp.ofLp (sourceCoord a «λ» j x)))‖ ≤ _
        exact (norm_add_le _ _).trans (by rw [norm_d]; exact add_le_add hm hp)
      calc
        «λ» j * ‖fcoord a «λ» x j‖ ≤ «λ» j * (‖sourceCoord a «λ» j x‖ + ‖x‖) :=
          mul_le_mul_of_nonneg_left hf («hλ» j).le
        _ = «λ» j * ‖sourceCoord a «λ» j x‖ + «λ» j * ‖x‖ := mul_add _ _ _
    · exact hx.1.add (hsum.mul_right ‖x‖)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hx.2.const_mul a.upperConstant)
    · intro j; exact norm_nonneg _
    · intro j
      change ‖a.linearMap (fcoord a «λ» x j)‖ ≤ a.upperConstant *
        ‖GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap) j
          (sourceCoord a «λ» j x)‖
      rw [fcoord,GeneralGraphCoordinate.map_forward,tilde_eq_pair]
      exact a.norm_h_le _

theorem backward_admissible (y : Target a «λ») :
    WeightedGraph.Admissible (GraphSplitting.Domain (fun _ : ℕ => A) ScalarL2)
      (GraphSplitting.Codomain (fun _ : ℕ => H) ScalarL2)
      (GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => a.linearMap))
      «λ» (bcoord a «λ» y) := by
  have hy := WeightedGraph.coordinates_admissible _ _ _ _ «hλ» y
  constructor
  · apply Summable.of_nonneg_of_le (fun j => mul_nonneg («hλ» j).le (norm_nonneg _))
    · intro j
      have hQ : ‖a.linearMap (targetCoord a «λ» j y)‖ ≤ ‖y‖ :=
        WeightedGraph.norm_image_coord_le _ _ _ _ «hλ» j y
      have hb : ‖bcoord a «λ» y j‖ ≤ ‖targetCoord a «λ» j y‖ + 2 * (a.lowerConstant⁻¹ * ‖y‖) :=
        (norm_bcoord_le a «λ» y j).trans (by
          have hi := mul_le_mul_of_nonneg_left hQ (inv_nonneg.mpr a.lower_pos.le)
          linarith)
      calc
        «λ» j * ‖bcoord a «λ» y j‖ ≤ «λ» j * (‖targetCoord a «λ» j y‖ + 2 * (a.lowerConstant⁻¹ * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hb («hλ» j).le
        _ = «λ» j * ‖targetCoord a «λ» j y‖ + «λ» j * (2 * (a.lowerConstant⁻¹ * ‖y‖)) := mul_add _ _ _
    · exact hy.1.add (hsum.mul_right (2 * (a.lowerConstant⁻¹ * ‖y‖)))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hy.2.const_mul a.lowerConstant⁻¹)
    · intro j; exact norm_nonneg _
    · intro j
      change ‖GraphSplitting.tilde (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2
        (fun _ => a.linearMap) j (bcoord a «λ» y j)‖ ≤ a.lowerConstant⁻¹ * ‖a.linearMap (targetCoord a «λ» j y)‖
      rw [tilde_bcoord]
      exact a.norm_h_symm_le _

def forward (x : Source a «λ») : Target a «λ» :=
  WeightedGraph.ofCoordinates _ _ _ «λ» «hλ» (fcoord a «λ» x) (forward_admissible a «λ» «hλ» hsum x)

def backward (y : Target a «λ») : Source a «λ» :=
  WeightedGraph.ofCoordinates _ _ _ «λ» «hλ» (bcoord a «λ» y) (backward_admissible a «λ» «hλ» hsum y)

@[simp] theorem coord_forward (j : ℕ) (x : Source a «λ») :
    targetCoord a «λ» j (forward a «λ» «hλ» hsum x) = fcoord a «λ» x j :=
  WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ» _ _ j

@[simp] theorem coord_backward (j : ℕ) (y : Target a «λ») :
    sourceCoord a «λ» j (backward a «λ» «hλ» hsum y) = bcoord a «λ» y j :=
  WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ» _ _ j

theorem backward_forward (x : Source a «λ») : backward a «λ» «hλ» hsum (forward a «λ» «hλ» hsum x) = x := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_backward]
  change WithLp.toLp 1 (GeneralGraphCoordinate.backward a (targetCoord a «λ» j (forward a «λ» «hλ» hsum x))) = _
  rw [coord_forward]
  change WithLp.toLp 1 (GeneralGraphCoordinate.backward a
    (GeneralGraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j x)))) = _
  rw [GeneralGraphCoordinate.backward_forward, WithLp.toLp_ofLp]

theorem forward_backward (y : Target a «λ») : forward a «λ» «hλ» hsum (backward a «λ» «hλ» hsum y) = y := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_forward]
  change GeneralGraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j (backward a «λ» «hλ» hsum y))) = _
  rw [coord_backward]
  change GeneralGraphCoordinate.forward a (GeneralGraphCoordinate.backward a (targetCoord a «λ» j y)) = _
  exact GeneralGraphCoordinate.forward_backward a _

def equiv : Source a «λ» ≃ Target a «λ» where
  toFun := forward a «λ» «hλ» hsum
  invFun := backward a «λ» «hλ» hsum
  left_inv := backward_forward a «λ» «hλ» hsum
  right_inv := forward_backward a «λ» «hλ» hsum

theorem forward_zero : forward a «λ» «hλ» hsum 0 = 0 := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [coord_forward, map_zero]
  change GeneralGraphCoordinate.forward a (WithLp.ofLp (sourceCoord a «λ» j 0)) = 0
  rw [map_zero]
  exact GeneralGraphCoordinate.forward_zero a

end GeneralGraphChange
end BanachGeometry
