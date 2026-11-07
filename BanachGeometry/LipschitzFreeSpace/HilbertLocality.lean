/- Finite-family neighborhood assembly for the actual output defect.
The final target is the coordinate specialization of upstream LocalOrthogonality,
not the general finite-dimensional-head/increment theorem R6 8.1.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.HilbertDefect
import BanachGeometry.HilbertSums.Nonlinear.SeparatedSupports
import BanachGeometry.HilbertSums.Nonlinear.Defect

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertFreeSpace
open BanachGeometry.HilbertSums BanachGeometry.HilbertSums.Nonlinear

/-- Includes the empty family, where radius 1 is valid. -/
theorem finite_positive_lower_bound {I : Type*} [Fintype I] (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ a i := by
  classical
  have hs : ∀ s : Finset I, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min (a i) ε, lt_min (ha i) hε, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound j hj)
  obtain ⟨ε, hε, hbound⟩ := hs Finset.univ
  exact ⟨ε, hε, fun i => hbound i (Finset.mem_univ i)⟩

/-- A common radius and a common block cutoff for every pair of a finite family. -/
theorem finite_local_direction_supports (c : ℝ) (hc : 0 < c) {I : Type} [Fintype I]
    (y : I → GradedHilbert) (hy : Function.Injective y) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ i j, i ≠ j → ∀ n, N ≤ n → ∀ u v,
      ‖u - y i‖ < ε → ‖v - y j‖ < ε →
      Disjoint (scalarSupport n (pointDirection c hc u n)) (scalarSupport n (pointDirection c hc v n)) := by
  classical
  let P := {p : I × I // p.1 ≠ p.2}
  have hpair (p : P) := pair_local_direction_supports c hc
    (show y p.val.1 ≠ y p.val.2 from fun h => p.property (hy h))
  choose ε hε N hN using hpair
  obtain ⟨δ, hδ, hδε⟩ := finite_positive_lower_bound ε hε
  let L := Finset.univ.sup N
  refine ⟨δ, hδ, L, ?_⟩
  intro i j hij n hn u v hu hv
  let p : P := ⟨(i, j), hij⟩
  have hNL : N p ≤ L := Finset.le_sup (f := N) (Finset.mem_univ p)
  exact hN p n (hNL.trans hn) u v (hu.trans_le (hδε p)) (hv.trans_le (hδε p))

/-- The actual defect has locally pairwise disjoint tail coordinate supports. -/
theorem hilbertDefect_localOrthogonality (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    BanachGeometry.LipschitzFreeGeometry.CoordinateLocality.LocalOrthogonality
      (fun z : Base => flattenEquiv (hilbertDefect c hc hc' z)) := by
  classical
  intro I _ z hz
  let y : I → GradedHilbert := fun i => hilbertEquiv c hc hc' (z i)
  have hy : Function.Injective y := (hilbertEquiv c hc hc').injective.comp hz
  obtain ⟨ε, hε, N, hN⟩ := finite_local_direction_supports c hc y hy
  let L : ℝ := 1 + 4 * c
  have hL : 0 < L := by dsimp [L]; positivity
  let δ := ε / L
  have hδ : 0 < δ := div_pos hε hL
  let S : I → Set (Σ n, BlockCoordinate n) := fun i =>
    {a | N ≤ a.1 ∧ ∃ x : Base, x ∈ Metric.ball (z i) δ ∧
      a.2 ∈ scalarSupport a.1 (pointDirection c hc (hilbertEquiv c hc hc' x) a.1)}
  have himage (i : I) (x : Base) (hx : x ∈ Metric.ball (z i) δ) :
      ‖hilbertEquiv c hc hc' x - y i‖ < ε := by
    have hdist : ‖x - z i‖ < ε / L := by simpa [Metric.mem_ball, dist_eq_norm, δ] using hx
    have hm : ‖x - z i‖ * L < ε := (lt_div_iff₀ hL).mp hdist
    exact ((hilbertEquiv_bounds c hc hc' x (z i)).2).trans_lt (by simpa [L, mul_comm] using hm)
  refine ⟨δ, hδ, N, S, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨n, a⟩ ⟨hn, x, hx, hxa⟩ ⟨_, x', hx', hx'a⟩
    have hd := hN i j hij n hn (hilbertEquiv c hc hc' x) (hilbertEquiv c hc hc' x')
      (himage i x hx) (himage j x' hx')
    exact Set.disjoint_left.mp hd hxa hx'a
  · intro i x hx
    rw [BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.mem_space]
    rintro ⟨n, a⟩ ha
    rw [BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates.tail_coord]
    by_cases hn : N ≤ n
    · rw [if_pos hn]
      apply defect_scalar_zero_of_direction_zero c hc hc' x n a
      by_contra hnonzero
      exact ha ⟨hn, x, hx, hnonzero⟩
    · rw [if_neg hn]

end BanachGeometry.HilbertFreeSpace
