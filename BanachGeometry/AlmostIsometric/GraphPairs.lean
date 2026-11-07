import BanachGeometry.NoC0.NoC0Closure
import BanachGeometry.AlmostIsometric.OptimalLipschitz
import BanachGeometry.HilbertSums.L2Separable

/-! Graph-pair reduction with an ordinary record of the displayed graph data.
No QuantitativeHilbertData, d/h/norm-preservation, or nontrivial A/H assumption
is added to the graph-pair statement.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace AlmostIsometricGraphPairs

structure GraphPair (L : ℝ) where
  A : Type
  H : Type
  [normedAddCommGroupA : NormedAddCommGroup A]
  [normedSpaceA : NormedSpace ℝ A]
  [completeSpaceA : CompleteSpace A]
  [separableSpaceA : SeparableSpace A]
  [normedAddCommGroupH : NormedAddCommGroup H]
  [innerProductSpaceH : InnerProductSpace ℝ H]
  [completeSpaceH : CompleteSpace H]
  [separableSpaceH : SeparableSpace H]
  linearMap : A →L[ℝ] H
  no_c0 : ¬ ContainsLinearCopy ScalarC0 A
  completelyContinuous : CompletelyContinuous linearMap
  weights : ℕ → ℝ
  weights_pos : ∀ j, 0 < weights j
  weights_summable : Summable weights
  weights_sum_le_one : (∑' j, weights j) ≤ 1
  psi : PointedBiLip
    (GraphSplitting.X (fun _ : ℕ => A) (fun _ : ℕ => H) ScalarL2 (fun _ => linearMap) weights)
    (WeightedGraph.Space (fun _ : ℕ => A) (fun _ : ℕ => H) (fun _ => linearMap) weights) L

attribute [instance] GraphPair.normedAddCommGroupA GraphPair.normedSpaceA
  GraphPair.completeSpaceA GraphPair.separableSpaceA GraphPair.normedAddCommGroupH
  GraphPair.innerProductSpaceH GraphPair.completeSpaceH GraphPair.separableSpaceH

namespace GraphPair
variable {L : ℝ} (p : GraphPair L)
abbrev X := GraphSplitting.X (fun _ : ℕ => p.A) (fun _ : ℕ => p.H) ScalarL2 (fun _ => p.linearMap) p.weights
abbrev Y := WeightedGraph.Space (fun _ : ℕ => p.A) (fun _ : ℕ => p.H) (fun _ => p.linearMap) p.weights

instance nontrivial_X : Nontrivial p.X := by
  letI : Nontrivial (GraphSplitting.Domain (fun _ : ℕ => p.A) ScalarL2 0) := by
    refine ⟨⟨WithLp.toLp 1 ((0 : p.A), CanonicalSequences.l2Basis 0),
      WithLp.toLp 1 ((0 : p.A), (0 : ScalarL2)), ?_⟩⟩
    intro h
    have ht : CanonicalSequences.l2Basis 0 = 0 :=
      congrArg (fun z : WithLp 1 (p.A × ScalarL2) => (WithLp.ofLp z).2) h
    have hn := CanonicalSequences.norm_l2Basis 0
    rw [ht, norm_zero] at hn
    norm_num at hn
  exact WeightedGraph.graph_nontrivial _ _ _ _ p.weights_pos
instance nontrivial_Y : Nontrivial p.Y := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne p.X
  exact ⟨⟨p.psi.equiv x,p.psi.equiv y,fun h => hxy (p.psi.equiv.injective h)⟩⟩

def xBanach : SeparableRealBanach := by
  letI : SeparableSpace ScalarL2 := HilbertSums.lp_two_separable
  exact { Carrier := p.X }
def yBanach : SeparableRealBanach where
  Carrier := p.Y

def splitting : p.X ≃L[ℝ] (p.Y × C0L2) :=
  (GraphSplitting.equiv _ _ _ _ p.weights p.weights_pos p.weights_summable p.weights_sum_le_one).trans
    ((ContinuousLinearEquiv.refl ℝ p.Y).prodCongr
      (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).toContinuousLinearEquiv)

theorem isometric_complemented : ∃ (J : C0L2 →L[ℝ] p.X) (P : p.X →L[ℝ] C0L2),
    (∀ v, ‖J v‖ = ‖v‖) ∧ ‖P‖ ≤ 1 ∧ P.comp J = ContinuousLinearMap.id ℝ C0L2 := by
  let e := C0Sum.homogeneousLinearIsometryEquiv ScalarL2
  let I := GraphSplitting.includeRight (fun _ : ℕ => p.A) (fun _ : ℕ => p.H)
    ScalarL2 (fun _ => p.linearMap) p.weights p.weights_pos p.weights_summable p.weights_sum_le_one
  let R := GraphSplitting.second (fun _ : ℕ => p.A) (fun _ : ℕ => p.H) ScalarL2 (fun _ => p.linearMap) p.weights
  let J := I.comp e.symm.toLinearIsometry.toContinuousLinearMap
  let P := e.toLinearIsometry.toContinuousLinearMap.comp R
  refine ⟨J,P,?_,?_,?_⟩
  · intro v
    change ‖I (e.symm v)‖ = ‖v‖
    rw [GraphSplitting.norm_includeRight,e.symm.norm_map]
  · apply P.opNorm_le_bound zero_le_one
    intro x
    change ‖e (R x)‖ ≤ 1 * ‖x‖
    rw [e.norm_map,one_mul]
    exact GraphSplitting.norm_second_le _ _ _ _ _ x
  · apply ContinuousLinearMap.ext
    intro v
    change e (R (I (e.symm v))) = v
    rw [GraphSplitting.second_includeRight,e.apply_symm_apply]
end GraphPair

def metricFamily (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i) (ht : Tendsto L atTop (nhds 1))
    (s : ∀ i, GraphPair (L i)) : AlmostIsometricFamily where
  X i := (s i).xBanach
  Y i := (s i).yBanach
  bound := L
  one_le := hL
  tends_one := ht
  psi i := (s i).psi

theorem hasContractivelyComplementedCopy_metricFamily (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i) (ht : Tendsto L atTop (nhds 1))
    (s : ∀ i, GraphPair (L i)) : (metricFamily L hL ht s).HasContractivelyComplementedCopy := fun i => (s i).isometric_complemented

theorem hasCoordinateSplitting_metricFamily (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i) (ht : Tendsto L atTop (nhds 1))
    (s : ∀ i, GraphPair (L i)) : (metricFamily L hL ht s).HasCoordinateSplitting := fun i => ⟨(s i).splitting⟩

theorem excludesFiniteSumCopy_metricFamily (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i) (ht : Tendsto L atTop (nhds 1))
    (s : ∀ i, GraphPair (L i)) : (metricFamily L hL ht s).ExcludesFiniteSumCopy := by
  intro q indices
  exact WeightedGraph.finite_no_c0L2 q
    (fun r _ => (s (indices r)).A) (fun r _ => (s (indices r)).H)
    (fun r _ => (s (indices r)).linearMap) (fun r => (s (indices r)).weights)
    (fun r => (s (indices r)).weights_pos)
    (fun r _ => (s (indices r)).completelyContinuous)
    (fun r _ => (s (indices r)).no_c0)

theorem exists_almostIsometric_nonisomorphic_pair_of_sequence (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i) (ht : Tendsto L atTop (nhds 1))
    (s : ∀ i, GraphPair (L i)) : ExistsAlmostIsometricNonisomorphicPair :=
  (metricFamily L hL ht s).exists_almostIsometric_nonisomorphic_pair_of_complemented_splitting_exclusion
    (hasContractivelyComplementedCopy_metricFamily L hL ht s) (hasCoordinateSplitting_metricFamily L hL ht s) (excludesFiniteSumCopy_metricFamily L hL ht s)

theorem exists_almostIsometric_nonisomorphic_pair_of_arbitrarily_accurate_graph_pairs
    (h : ∀ η : ℝ, 0 < η → Nonempty (GraphPair (1+η))) : ExistsAlmostIsometricNonisomorphicPair := by
  let L := fun i => 1 + ApproximationParameters.theta i
  have hL (i : ℕ) : 1 ≤ L i := by dsimp [L]; linarith [ApproximationParameters.theta_pos i]
  have ht : Tendsto L atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add ApproximationParameters.theta_tendsto
  let s : ∀ i, GraphPair (L i) := fun i => Classical.choice (h _ (ApproximationParameters.theta_pos i))
  exact exists_almostIsometric_nonisomorphic_pair_of_sequence L hL ht s

end AlmostIsometricGraphPairs
end BanachGeometry
