/- The coordinate hypothesis used by the constructed map implies the general R6 increment hypothesis.
The finite-dimensional head and the closed orthogonal tail subspaces are constructed explicitly.
This is an implication between the two hypotheses, not an identification of their scopes.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.GeneralCriterion

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry
open BanachGeometry.LipschitzFreeGeometry.HilbertCoordinates

universe uM uIndex
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

/-- No infinite-dimensional block is concealed in the finite head. -/
theorem finiteDimensional_coordinate_head (N : ℕ) :
    FiniteDimensional ℝ (space (headSet (ι := ι) N)) := by
  classical
  let F := space (headSet (ι := ι) N)
  let T : F →ₗ[ℝ] (∀ n : Fin N, EuclideanSpace ℝ (ι n.val)) :=
    { toFun := fun x n => x.val n.val
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  apply Module.Finite.of_injective T
  intro x y hxy
  apply Subtype.ext
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  by_cases hn : n < N
  · have he := congrArg (fun v => v (⟨n, hn⟩ : Fin N)) hxy
    exact congrArg (fun v => v a) he
  · have hnot : (⟨n, a⟩ : Σ n, ι n) ∉ headSet N := hn
    rw [(mem_space (headSet N) x.val).mp x.property ⟨n, a⟩ hnot,
      (mem_space (headSet N) y.val).mp y.property ⟨n, a⟩ hnot]

theorem mem_coordinate_space_inter {S T : Set (Σ n, ι n)} {x : Hilbert (ι := ι)}
    (hS : x ∈ space S) (hT : x ∈ space T) : x ∈ space (S ∩ T) := by
  rw [mem_space]
  intro a ha
  by_cases hs : a ∈ S
  · exact (mem_space T x).mp hT a (fun ht => ha ⟨hs, ht⟩)
  · exact (mem_space S x).mp hS a hs

/-- Coordinate tail separation is sufficient for the general increment condition. -/
theorem incrementLocality_of_coordinateLocalOrthogonality {M : Type uM} [MetricSpace M]
    (D : M → Hilbert (ι := ι)) (hloc : CoordinateLocality.LocalOrthogonality D) : IncrementLocality D := by
  intro I _ z hz
  obtain ⟨r, hr, N, S, hS, hDS⟩ := hloc z hz
  let F := space (headSet (ι := ι) N)
  let K : I → Submodule ℝ (Hilbert (ι := ι)) := fun i => space (S i ∩ tailSet N)
  refine ⟨fun i => Metric.ball (z i) r, fun i => ⟨Metric.isOpen_ball, Metric.mem_ball_self hr⟩,
    F, finiteDimensional_coordinate_head N, K, ?_, ?_, ?_⟩
  · intro i
    refine ⟨space_isClosed _, ?_⟩
    intro k hk
    rw [Submodule.mem_orthogonal]
    intro f hf
    apply inner_eq_zero_of_disjoint (x := f) (y := k) ?_ hf hk
    apply Set.disjoint_left.mpr
    rintro ⟨n, a⟩ hn ⟨_, ht⟩
    change n < N at hn
    change N ≤ n at ht
    exact (not_lt_of_ge ht) hn
  · intro i j hij u hu v hv
    apply inner_eq_zero_of_disjoint (x := u) (y := v) ?_ hu hv
    exact (hS hij).mono (Set.inter_subset_left) (Set.inter_subset_left)
  · intro i x hx y hy
    have htail (w : M) (hw : w ∈ Metric.ball (z i) r) : tail N (D w) ∈ K i :=
      mem_coordinate_space_inter (hDS i w hw) (projection_mem (tailSet N) (D w))
    apply Submodule.mem_sup.mpr
    refine ⟨head N (D x - D y), projection_mem (headSet N) _, tail N (D x - D y), ?_, head_add_tail _ _⟩
    rw [map_sub]
    exact (K i).sub_mem (htail x hx) (htail y hy)

end BanachGeometry.LipschitzFreeLocalization
