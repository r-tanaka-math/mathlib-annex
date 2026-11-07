import BanachGeometry.OperatorGraphs.GraphSplitting
import BanachGeometry.OperatorGraphs.GraphSupport
import BanachGeometry.HilbertSums.L2Separable

/-! Graph X/Y Banach bundles from the abstract QuantitativeHilbertData
boundary. The splitting and the exact H2-style isometric/contractive pair
are explicit. This module works with those fields for arbitrary supplied
Banach and Hilbert bundles, without choosing a concrete free-space model. -/

noncomputable section
namespace BanachGeometry
namespace OperatorGraphPair
variable {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) («λ» : ℕ → ℝ)

abbrev Y := WeightedGraph.Space (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) (fun _ => a.linearMap) «λ»
abbrev X := GraphSplitting.X (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier) ScalarL2 (fun _ => a.linearMap) «λ»

def yBanach («hλ» : ∀ j, 0 < «λ» j) : SeparableRealBanach := by
  letI : Nontrivial (Y a «λ») := WeightedGraph.graph_nontrivial _ _ _ _ «hλ»
  exact { Carrier := Y a «λ» }

def xBanach («hλ» : ∀ j, 0 < «λ» j) : SeparableRealBanach := by
  letI : TopologicalSpace.SeparableSpace ScalarL2 := HilbertSums.lp_two_separable
  letI : Nontrivial (X a «λ») := WeightedGraph.graph_nontrivial _ _ _ _ «hλ»
  exact { Carrier := X a «λ» }

def splitting («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ») (hθ : (∑' j, «λ» j) ≤ 1) :
    X a «λ» ≃L[ℝ] (Y a «λ» × C0L2) :=
  (GraphSplitting.equiv _ _ _ _ «λ» «hλ» hsum hθ).trans
    ((ContinuousLinearEquiv.refl ℝ (Y a «λ»)).prodCongr
      (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).toContinuousLinearEquiv)

theorem isometric_complemented («hλ» : ∀ j, 0 < «λ» j) (hsum : Summable «λ»)
    (hθ : (∑' j, «λ» j) ≤ 1) :
    ∃ (J : C0L2 →L[ℝ] X a «λ») (P : X a «λ» →L[ℝ] C0L2),
      (∀ v, ‖J v‖ = ‖v‖) ∧ ‖P‖ ≤ 1 ∧ P.comp J = ContinuousLinearMap.id ℝ C0L2 := by
  let e := C0Sum.homogeneousLinearIsometryEquiv ScalarL2
  let I := GraphSplitting.includeRight (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier)
    ScalarL2 (fun _ => a.linearMap) «λ» «hλ» hsum hθ
  let R := GraphSplitting.second (fun _ : ℕ => A.Carrier) (fun _ : ℕ => H.Carrier)
    ScalarL2 (fun _ => a.linearMap) «λ»
  let J := I.comp e.symm.toLinearIsometry.toContinuousLinearMap
  let P := e.toLinearIsometry.toContinuousLinearMap.comp R
  refine ⟨J, P, ?_, ?_, ?_⟩
  · intro v
    change ‖I (e.symm v)‖ = ‖v‖
    rw [GraphSplitting.norm_includeRight, e.symm.norm_map]
  · apply P.opNorm_le_bound zero_le_one
    intro x
    change ‖e (R x)‖ ≤ 1 * ‖x‖
    rw [e.norm_map, one_mul]
    exact GraphSplitting.norm_second_le _ _ _ _ _ x
  · apply ContinuousLinearMap.ext
    intro v
    change e (R (I (e.symm v))) = v
    rw [GraphSplitting.second_includeRight, e.apply_symm_apply]

end OperatorGraphPair
end BanachGeometry
