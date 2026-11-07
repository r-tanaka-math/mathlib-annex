import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality

noncomputable section
open scoped NNReal InnerProductSpace
open BanachGeometry

example (X Y : SeparableRealBanach) (h : AlmostIsometricAtEveryTolerance X Y) :
    (LipschitzDistance.distortions X.Carrier Y.Carrier).Nonempty ∧
    BddBelow (LipschitzDistance.distortions X.Carrier Y.Carrier) ∧
    LipschitzDistance.finiteDistance X.Carrier Y.Carrier = 1 :=
  ⟨LipschitzDistance.distortions_nonempty_of_almostIsometric X Y h,
    LipschitzDistance.bddBelow_distortions _ _, LipschitzDistance.finiteDistance_eq_one X Y h⟩

example {M N : Type*} [MetricSpace M] [MetricSpace N] (f : M → N) {K : ℝ≥0}
    (hf : LipschitzWith K f) : IsLeast (OptimalLipschitz.bounds f) (OptimalLipschitz.finiteConstant f) :=
  OptimalLipschitz.isLeast_bounds f (OptimalLipschitz.bounds_nonempty_of_lipschitzWith f hf)

example (A B : ℕ → Type) [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (j : ℕ) :
    ‖WeightedGraph.coord A B Q w j‖ ≤ (w j)⁻¹ :=
  WeightedGraph.opNorm_coord_le A B Q w hw j

example (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) {I : Type} [Fintype I]
    (z : I → HilbertFreeSpace.Base) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l : ℕ, 1 ≤ l ∧
      ∃ K : I → Submodule ℝ HilbertSums.Nonlinear.FlatHilbert,
      (∀ i, IsClosed (K i : Set HilbertSums.Nonlinear.FlatHilbert) ∧
        K i ≤ BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.space
          (BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.tailSet l)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) ∧
      ∀ i x, x ∈ Metric.ball (z i) δ →
        BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.tail l
          (HilbertSums.Nonlinear.flattenEquiv (HilbertSums.Nonlinear.hilbertDefect c hc hc' x)) ∈ K i :=
  HilbertFreeSpace.exists_positive_closed_orthogonal_tail_neighborhoods c hc hc' z hz

example (l n : ℕ) : l < n + 1 ↔ l ≤ n := by omega

example (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) {I : Type} [Fintype I]
    (z : I → HilbertFreeSpace.Base) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l : ℕ, 1 ≤ l ∧
      ∃ K : I → Submodule ℝ HilbertSums.Nonlinear.GradedHilbert,
      (∀ i, IsClosed (K i : Set HilbertSums.Nonlinear.GradedHilbert) ∧
        K i ≤ (BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.space
          (BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.tailSet l)).comap
            HilbertSums.Nonlinear.flattenEquiv.toLinearEquiv.toLinearMap) ∧
      (∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) ∧
      ∀ i x, x ∈ Metric.ball (z i) δ →
        HilbertSums.blockTail l (HilbertSums.Nonlinear.hilbertDefect c hc hc' x) ∈ K i :=
  HilbertFreeSpace.exists_positive_closed_orthogonal_graded_tail_neighborhoods c hc hc' z hz

-- The final finite-distance theorem has actual nontrivial witnesses.
example : Nontrivial AlmostIsometricPair.xSpace.Carrier := inferInstance
example : Nontrivial AlmostIsometricPair.ySpace.Carrier := inferInstance

-- Both bundle and every-tolerance predicate are expanded in this direct type.
example : ∃ X Y : Type, ∃ nx : NormedAddCommGroup X, ∃ ny : NormedAddCommGroup Y,
    letI := nx; letI := ny
    ∃ sx : NormedSpace ℝ X, ∃ sy : NormedSpace ℝ Y,
    letI := sx; letI := sy
    CompleteSpace X ∧ CompleteSpace Y ∧ TopologicalSpace.SeparableSpace X ∧
      TopologicalSpace.SeparableSpace Y ∧ Nontrivial X ∧ Nontrivial Y ∧
      IsEmpty (X ≃L[ℝ] Y) ∧ ∀ ε : ℝ, 0 < ε → ∃ f : X ≃ Y,
        f 0 = 0 ∧ (∀ x x', ‖f x - f x'‖ ≤ (1 + ε) * ‖x - x'‖) ∧
          (∀ y y', ‖f.symm y - f.symm y'‖ ≤ (1 + ε) * ‖y - y'‖) := by
  refine ⟨AlmostIsometricPair.xSpace.Carrier, AlmostIsometricPair.ySpace.Carrier,
    AlmostIsometricPair.xSpace.normedAddCommGroup, AlmostIsometricPair.ySpace.normedAddCommGroup,
    AlmostIsometricPair.xSpace.normedSpace, AlmostIsometricPair.ySpace.normedSpace,
    AlmostIsometricPair.xSpace.completeSpace, AlmostIsometricPair.ySpace.completeSpace,
    AlmostIsometricPair.xSpace.separableSpace, AlmostIsometricPair.ySpace.separableSpace,
    AlmostIsometricPair.xSpace.nontrivial, AlmostIsometricPair.ySpace.nontrivial, AlmostIsometricPair.nonisomorphic, ?_⟩
  exact fun ε hε => AlmostIsometricPair.exists_pointed_equiv ε hε
