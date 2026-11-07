import BanachGeometry.LipschitzFreeSpace.HilbertLocality
import BanachGeometry.LipschitzFreeSpace.Localization.CoordinateBridge

/-! Positive cutoffs and closed orthogonal coordinate tails for the Hilbert defect.
Blocks have source index n and paper index n+1. Thus paper Q_l retains n+1>l,
which is exactly the source predicate l≤n, not source tail (l+1). -/
noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertFreeSpace
open BanachGeometry.HilbertSums BanachGeometry.HilbertSums.Nonlinear
open BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates


theorem finite_local_direction_supports_positive (c : ℝ) (hc : 0 < c)
    {I : Type} [Fintype I] (y : I → GradedHilbert) (hy : Function.Injective y) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ l : ℕ, 1 ≤ l ∧ ∀ i j, i ≠ j → ∀ n, l ≤ n → ∀ u v,
      ‖u - y i‖ < ε → ‖v - y j‖ < ε →
      Disjoint (scalarSupport n (pointDirection c hc u n))
        (scalarSupport n (pointDirection c hc v n)) := by
  obtain ⟨ε, hε, N, hN⟩ := finite_local_direction_supports c hc y hy
  refine ⟨ε, hε, N + 1, by omega, ?_⟩
  intro i j hij n hn u v hu hv
  exact hN i j hij n (by omega) u v hu hv

theorem exists_positive_closed_orthogonal_tail_neighborhoods
    (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) {I : Type} [Fintype I]
    (z : I → Base) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l : ℕ, 1 ≤ l ∧ ∃ K : I → Submodule ℝ FlatHilbert,
      (∀ i, IsClosed (K i : Set FlatHilbert) ∧ K i ≤ space (tailSet l)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) ∧
      ∀ i x, x ∈ Metric.ball (z i) δ →
        tail l (flattenEquiv (hilbertDefect c hc hc' x)) ∈ K i := by
  classical
  let y : I → GradedHilbert := fun i => hilbertEquiv c hc hc' (z i)
  have hy : Function.Injective y := (hilbertEquiv c hc hc').injective.comp hz
  obtain ⟨ε, hε, l, hl, hN⟩ := finite_local_direction_supports_positive c hc y hy
  let L : ℝ := 1 + 4 * c
  have hL : 0 < L := by dsimp [L]; positivity
  let δ := ε / L
  have hδ : 0 < δ := div_pos hε hL
  let S : I → Set (Σ n, BlockCoordinate n) := fun i =>
    {a | l ≤ a.1 ∧ ∃ x : Base, x ∈ Metric.ball (z i) δ ∧
      a.2 ∈ scalarSupport a.1 (pointDirection c hc (hilbertEquiv c hc hc' x) a.1)}
  have himage (i : I) (x : Base) (hx : x ∈ Metric.ball (z i) δ) :
      ‖hilbertEquiv c hc hc' x - y i‖ < ε := by
    have hdist : ‖x - z i‖ < ε / L := by simpa [Metric.mem_ball, dist_eq_norm, δ] using hx
    have hm : ‖x - z i‖ * L < ε := (lt_div_iff₀ hL).mp hdist
    exact ((hilbertEquiv_bounds c hc hc' x (z i)).2).trans_lt (by simpa [L, mul_comm] using hm)
  have hS (i j : I) (hij : i ≠ j) : Disjoint (S i) (S j) := by
    apply Set.disjoint_left.mpr
    rintro ⟨n, a⟩ ⟨hn, x, hx, hxa⟩ ⟨_, x', hx', hx'a⟩
    exact Set.disjoint_left.mp
      (hN i j hij n hn (hilbertEquiv c hc hc' x) (hilbertEquiv c hc hc' x')
        (himage i x hx) (himage j x' hx')) hxa hx'a
  refine ⟨δ, hδ, l, hl, fun i => space (S i), ?_, ?_, ?_⟩
  · intro i
    refine ⟨space_isClosed _, ?_⟩
    intro u hu
    rw [mem_space]
    intro a ha
    exact (mem_space (S i) u).mp hu a (fun hs => ha hs.1)
  · intro i j hij u hu v hv
    exact inner_eq_zero_of_disjoint (hS i j hij) hu hv
  · intro i x hx
    rw [mem_space]
    rintro ⟨n, a⟩ ha
    rw [tail_coord]
    by_cases hn : l ≤ n
    · rw [if_pos hn]
      apply defect_scalar_zero_of_direction_zero c hc hc' x n a
      by_contra hnonzero
      exact ha ⟨hn, x, hx, hnonzero⟩
    · rw [if_neg hn]

/-- The paper tail and the block tail commute with the concrete coordinate isometry. -/
theorem flattenEquiv_blockTail (l : ℕ) (x : GradedHilbert) :
    flattenEquiv (HilbertSums.blockTail l x) = tail l (flattenEquiv x) := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  by_cases hn : n < l
  · simp [flattenEquiv_apply, HilbertSums.blockTail_apply, tail_coord, hn, show ¬ l ≤ n by omega]
  · simp [flattenEquiv_apply, HilbertSums.blockTail_apply, tail_coord, hn, show l ≤ n by omega]

/-- Closedness is transported by continuous preimage, never by an arbitrary projection. -/
theorem exists_positive_closed_orthogonal_graded_tail_neighborhoods
    (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) {I : Type} [Fintype I]
    (z : I → Base) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l : ℕ, 1 ≤ l ∧ ∃ K : I → Submodule ℝ GradedHilbert,
      (∀ i, IsClosed (K i : Set GradedHilbert) ∧
        K i ≤ (space (tailSet l)).comap flattenEquiv.toLinearEquiv.toLinearMap) ∧
      (∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) ∧
      ∀ i x, x ∈ Metric.ball (z i) δ →
        HilbertSums.blockTail l (hilbertDefect c hc hc' x) ∈ K i := by
  obtain ⟨δ, hδ, l, hl, K, hK, horth, hmem⟩ :=
    exists_positive_closed_orthogonal_tail_neighborhoods c hc hc' z hz
  refine ⟨δ, hδ, l, hl, fun i => (K i).comap flattenEquiv.toLinearEquiv.toLinearMap,
    ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hK i).1.preimage flattenEquiv.continuous, fun u hu => (hK i).2 hu⟩
  · intro i j hij u hu v hv
    rw [← flattenEquiv.inner_map_map u v]
    exact horth i j hij _ hu _ hv
  · intro i x hx
    change flattenEquiv (HilbertSums.blockTail l (hilbertDefect c hc hc' x)) ∈ K i
    rw [flattenEquiv_blockTail]
    exact hmem i x hx

end BanachGeometry.HilbertFreeSpace
