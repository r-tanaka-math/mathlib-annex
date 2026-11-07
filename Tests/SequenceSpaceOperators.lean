import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.AlmostIsometric.Consequences
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality

/- Local execution status is recorded in the external qualification receipts. -/

noncomputable section
open BanachGeometry Filter TopologicalSpace

example (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (u : ℕ → L1Sum V) (hu : WeaklyCauchy u) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ m, N ≤ m → ∀ n, ‖L1Tails.tail V m (u n)‖ < ε :=
  WeakTailGliding.eventually_uniform_tail_bound_of_weaklyCauchy V u hu ε hε

example (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [SeparableSpace (B →L[ℝ] ℝ)] (T : B →L[ℝ] L1Sum V) :
    Tendsto (fun m => ‖(L1Tails.tail V m).comp T‖) atTop (nhds 0) :=
  L1Tails.tendsto_opNorm_tail_comp V T

example (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) : ContainsComplementedCopy L1C0L2 d.FixedX :=
  d.fixedX_contains_complemented h2

example (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy)
    (hNoY : ¬ ContainsComplementedCopy L1C0L2 d.FixedY) : ExistsAlmostIsometricNonisomorphicPair :=
  d.exists_almostIsometric_nonisomorphic_pair_of_complemented_obstruction h2 hNoY

example {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) (z : A.Carrier × ScalarL2) :
    GraphCoordinate.backward a (GraphCoordinate.forward a z) = z :=
  GraphCoordinate.backward_forward a z

example (n : ℕ) : (∑' m, ApproximationParameters.weight n m) = ApproximationParameters.theta n :=
  ApproximationParameters.weights_sum n

example (E G D : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (hG : ¬ ContainsLinearCopy E G) (hdual : SeparableSpace (D →L[ℝ] ℝ)) :
    ¬ ContainsComplementedCopy (L1Shifts.F E) (G × D) :=
  FinitePerturbation.no_complemented_l1 E G D hG hdual

example (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy)
    (hcorner : ∀ T : d.FixedY →L[ℝ] L1C0L2,
      Localization.JointCorner C0L2 (fun k => d.Z k) T)
    (hheads : ∀ n, ¬ ContainsComplementedCopy L1C0L2 (C0Sum.FiniteHead (fun k => d.Z k) n)) :
    ExistsAlmostIsometricNonisomorphicPair := d.exists_almostIsometric_nonisomorphic_pair_of_corner_and_head_exclusions h2 hcorner hheads

#print axioms L1Linear.continuousLinearMap
#print axioms L1DualBlocks.functional
#print axioms WeakTailGliding.hasUniformlySmallTails_of_weaklyCauchy
#print axioms SeparableDual.unit_sequence_subsequence
#print axioms L1Tails.tendsto_opNorm_tail_comp
#print axioms Factorization.repair_left_inverse
#print axioms Localization.through_projection_range
#print axioms AlmostIsometricFamily.fixedX_contains_complemented
#print axioms AlmostIsometricFamily.exists_almostIsometric_nonisomorphic_pair_of_complemented_obstruction
#print axioms WeightedGraph.isClosed_submodule
#print axioms WeightedGraph.norm_formula
#print axioms GraphCoordinate.equiv
#print axioms ApproximationParameters.bound_tendsto
#print axioms WeightedGraph.admissibleEquiv
#print axioms LinearExclusion.countable_of_finite
#print axioms L1Shifts.down_up
#print axioms L1Shifts.norm_down_comp
#print axioms FinitePerturbation.no_complemented_l1
#print axioms Localization.finite_head_of_joint_corner
#print axioms AlmostIsometricFamily.exists_almostIsometric_nonisomorphic_pair_of_corner_and_head_exclusions
