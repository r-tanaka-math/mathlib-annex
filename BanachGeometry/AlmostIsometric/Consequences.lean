import BanachGeometry.AlmostIsometric.GraphPairs
import BanachGeometry.OperatorGraphs.GeneralGraphBounds
import BanachGeometry.SequenceSpaces.WeightedL1
import BanachGeometry.LipschitzFreeGeometry.WeakSums
import BanachGeometry.LipschitzFreeSpace.UniversalProperties

/-! Full-statement adapters: literal real iSup for weak tails, actual finite Pi
localization, canonical interleaving, and the fixed-pair conclusion with complemented
copy, splitting and exclusion properties. Weak-Cauchy boundedness reuses the generic
Banach–Steinhaus proof in the preserved Apache-2.0 WeakSums port; no WSC assumption.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open scoped NNReal
open Filter TopologicalSpace
namespace BanachGeometry
namespace WeakTailGliding

theorem tendsto_iSup_norm_tail_of_weaklyCauchy (V : ℕ → Type*)
    [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    (u : ℕ → L1Sum V) (hu : WeaklyCauchy u) :
    Tendsto (fun m => ⨆ n, ‖L1Tails.tail V m (u n)‖) atTop (nhds 0) := by
  have hw : BanachGeometry.LipschitzFreeGeometry.WeakSequences.WeakCauchy u := hu
  obtain ⟨C,hC⟩ := BanachGeometry.LipschitzFreeGeometry.WeakSequences.WeakCauchy.bounded hw
  have hbd (m : ℕ) : BddAbove (Set.range (fun n => ‖L1Tails.tail V m (u n)‖)) := by
    refine ⟨C,?_⟩
    rintro _ ⟨n,rfl⟩
    exact (L1Tails.norm_tail_le V m (u n)).trans (hC n)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_uniform_tail_bound_of_weaklyCauchy V u hu (ε/2) (half_pos hε)
  refine ⟨M,?_⟩
  intro m hm
  have hnonneg : 0 ≤ ⨆ n, ‖L1Tails.tail V m (u n)‖ :=
    (norm_nonneg _).trans (le_ciSup (hbd m) 0)
  have hsmall : (⨆ n, ‖L1Tails.tail V m (u n)‖) ≤ ε/2 := ciSup_le (fun n => (hM m hm n).le)
  simpa only [dist_zero_right,Real.norm_of_nonneg hnonneg] using hsmall.trans_lt (half_lt_self hε)

end WeakTailGliding
namespace Corner

theorem finite_pi_localization (V : ℕ → Type*)
    [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    (h : ContainsComplementedCopy L1C0L2 (C0Sum V)) :
    ∃ n : ℕ, ContainsComplementedCopy L1C0L2 (∀ r : Fin n, V r.val) := by
  obtain ⟨n,hn⟩ := finite_head_localization C0L2 V h
  exact ⟨n,Factorization.complemented_transport
    (C0Sum.finiteHeadEquivPi V n).toContinuousLinearEquiv hn⟩

end Corner
namespace WeightedGraph

theorem opNorm_output_le (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ) : ‖output A B Q «λ»‖ ≤ 1 :=
  (output A B Q «λ»).opNorm_le_bound zero_le_one
    (fun x => by simpa only [one_mul] using norm_output_le A B Q «λ» x)

end WeightedGraph
namespace HilbertC0

theorem not_boundedBelow_of_coordinate_norm_null
    (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] C0Sum V) (u : ℕ → E) (hu : Orthonormal ℝ u)
    (hcoord : ∀ i, Tendsto (fun k => ‖T (u k) i‖) atTop (nhds 0)) :
    ¬ ∃ b : ℝ, 0 < b ∧ ∀ x, b*‖x‖ ≤ ‖T x‖ := by
  rintro ⟨b,hb,hlower⟩
  exact no_lower_of_coordinate_null V T u hu
    (fun i => tendsto_zero_iff_norm_tendsto_zero.mpr (hcoord i)) b hb hlower

end HilbertC0
namespace FiniteGraph

def interleaving (q : ℕ) (hq : 0 < q) : ℕ ≃ Fin q × ℕ := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact (Nat.divModEquiv q).trans (Equiv.prodComm _ _)

def canonicalEquiv (q : ℕ) (hq : 0 < q) (A B : Fin q → ℕ → Type)
    [∀ r j, NormedAddCommGroup (A r j)] [∀ r j, NormedSpace ℝ (A r j)]
    [∀ r j, NormedAddCommGroup (B r j)] [∀ r j, NormedSpace ℝ (B r j)]
    (Q : ∀ r j, A r j →L[ℝ] B r j) («λ» : Fin q → ℕ → ℝ) :
    Rows A B Q «λ» ≃L[ℝ] Flat A B Q «λ» (interleaving q hq) :=
  equiv A B Q «λ» (interleaving q hq) hq

theorem norm_le_norm_canonicalEquiv_and_le_mul_norm (q : ℕ) (hq : 0 < q) (A B : Fin q → ℕ → Type)
    [∀ r j, NormedAddCommGroup (A r j)] [∀ r j, NormedSpace ℝ (A r j)]
    [∀ r j, NormedAddCommGroup (B r j)] [∀ r j, NormedSpace ℝ (B r j)]
    (Q : ∀ r j, A r j →L[ℝ] B r j) («λ» : Fin q → ℕ → ℝ) (u : Rows A B Q «λ») :
    ‖u‖ ≤ ‖canonicalEquiv q hq A B Q «λ» u‖ ∧
      ‖canonicalEquiv q hq A B Q «λ» u‖ ≤ (q : ℝ)*‖u‖ :=
  ⟨norm_le_forward A B Q «λ» (interleaving q hq) u,norm_forward_le A B Q «λ» (interleaving q hq) hq u⟩

end FiniteGraph
namespace AlmostIsometricFamily

theorem fixed_pair_geometry (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) :
    LipschitzDistance.finiteOptimalDistance d.FixedX d.FixedY = 1 ∧
    ContainsComplementedCopy L1C0L2 d.FixedX ∧
    ¬ ContainsComplementedCopy L1C0L2 d.FixedY ∧
    IsEmpty (d.FixedX ≃L[ℝ] d.FixedY) ∧
    AlmostIsometricAtEveryTolerance d.fixedXBanach d.fixedYBanach := by
  refine ⟨LipschitzDistance.finiteOptimalDistance_eq_one d.fixedXBanach d.fixedYBanach
    d.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach,
    d.fixedX_contains_complemented h2,d.not_complemented_fixedY_of_splitting_and_finite_exclusion h3 h4,
    d.nonisomorphic_fixedX_fixedY_of_complemented_splitting_exclusion h2 h3 h4,
    d.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach⟩

end AlmostIsometricFamily
namespace AlmostIsometricGraphPairs

theorem fixed_pair_geometry_of_sequence (L : ℕ → ℝ) (hL : ∀ i, 1 ≤ L i)
    (ht : Tendsto L atTop (nhds 1)) (s : ∀ i, GraphPair (L i)) :
    let d := metricFamily L hL ht s
    LipschitzDistance.finiteOptimalDistance d.FixedX d.FixedY = 1 ∧
    ContainsComplementedCopy L1C0L2 d.FixedX ∧
    ¬ ContainsComplementedCopy L1C0L2 d.FixedY ∧
    IsEmpty (d.FixedX ≃L[ℝ] d.FixedY) ∧
    AlmostIsometricAtEveryTolerance d.fixedXBanach d.fixedYBanach :=
  (metricFamily L hL ht s).fixed_pair_geometry
    (hasContractivelyComplementedCopy_metricFamily L hL ht s) (hasCoordinateSplitting_metricFamily L hL ht s) (excludesFiniteSumCopy_metricFamily L hL ht s)

end AlmostIsometricGraphPairs
namespace LipschitzFreeProperties

theorem optimalConstant_eq_norm_linearize {M F : Type*} [MetricSpace M] [Zero M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : M → F) {L : ℝ≥0} (hg : LipschitzWith L g) (hg0 : g 0 = 0) :
    OptimalLipschitz.finiteConstant g = ‖BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize g‖ :=
  OptimalLipschitz.finiteConstant_eq_of_isLeast g ‖BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize g‖₊
    (isLeast_lipschitzConstants_linearize g hg hg0)

end LipschitzFreeProperties
end BanachGeometry
