import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cardinal bounds from dense subsets

A uniformly separated family injects into every dense subset.  The statements
use cardinalities of explicit dense subsets, not the cardinality of the whole
metric space.  The two universes remain independent.
-/

set_option autoImplicit false

open Function Metric Set
open scoped Cardinal

namespace MathlibAnnex.Topology

universe u v

/-- Choose different nearby points of a dense subset for a uniformly
separated family. -/
theorem exists_injective_into_dense_of_separated
    {I : Type u} {X : Type v} [PseudoMetricSpace X]
    (s : Set X) (hs : Dense s) (f : I → X) {ε : ℝ} (hε : 0 < ε)
    (hsep : Pairwise fun i j => ε ≤ dist (f i) (f j)) :
    ∃ g : I → s, Injective g := by
  classical
  have hnear (i : I) : ∃ y : s, dist (f i) (y : X) < ε / 3 := by
    obtain ⟨y, hy, hdist⟩ :=
      Metric.mem_closure_iff.mp (hs (f i)) (ε / 3) (by positivity)
    exact ⟨⟨y, hy⟩, hdist⟩
  choose g hg using hnear
  refine ⟨g, ?_⟩
  intro i j hij
  by_contra hne
  have hval : (g i : X) = (g j : X) := congrArg Subtype.val hij
  have htri := dist_triangle (f i) (g i : X) (f j)
  rw [hval, dist_comm (g j : X) (f j)] at htri
  have hlow := hsep hne
  have hi := hg i
  rw [hval] at hi
  have hj := hg j
  linarith

/-- A uniformly separated family has cardinality at most that of every
dense subset, with lifts for independent universes. -/
theorem cardinalMk_le_cardinalMk_dense_of_separated
    {I : Type u} {X : Type v} [PseudoMetricSpace X]
    (s : Set X) (hs : Dense s) (f : I → X) {ε : ℝ} (hε : 0 < ε)
    (hsep : Pairwise fun i j => ε ≤ dist (f i) (f j)) :
    Cardinal.lift.{v} (#I) ≤ Cardinal.lift.{u} (#s) := by
  obtain ⟨g, hg⟩ := exists_injective_into_dense_of_separated s hs f hε hsep
  exact Cardinal.lift_mk_le_lift_mk_of_injective hg

/-- A uniformly separated family is smaller than the continuum if the
ambient metric space has a dense subset smaller than the continuum. -/
theorem cardinalMk_lt_continuum_of_separated_of_dense
    {I : Type u} {X : Type v} [PseudoMetricSpace X]
    (s : Set X) (hs : Dense s) (hcard : #s < Cardinal.continuum)
    (f : I → X) {ε : ℝ} (hε : 0 < ε)
    (hsep : Pairwise fun i j => ε ≤ dist (f i) (f j)) :
    #I < Cardinal.continuum := by
  have hle := cardinalMk_le_cardinalMk_dense_of_separated s hs f hε hsep
  have hsmall : Cardinal.lift.{u} (#s) < Cardinal.continuum := by
    exact Cardinal.lift_lt_continuum.mpr hcard
  have hlt := hle.trans_lt hsmall
  exact Cardinal.lift_lt_continuum.mp hlt

/-- Restricting a continuous map with dense range to a dense subset keeps
the range dense.  This formulation also works for nonmetrizable spaces. -/
theorem denseRange_restrict_of_continuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hfrange : DenseRange f)
    (s : Set X) (hs : Dense s) :
    DenseRange (fun x : s => f x) := by
  let t : Set Y := Set.range (fun x : s => f x)
  have hclosed : IsClosed (f ⁻¹' closure t) := isClosed_closure.preimage hf
  have hsub : s ⊆ f ⁻¹' closure t := by
    intro x hx
    exact subset_closure ⟨⟨x, hx⟩, rfl⟩
  have hclsub : closure s ⊆ f ⁻¹' closure t :=
    hclosed.closure_subset_iff.mpr hsub
  intro y
  exact hfrange.induction_on y isClosed_closure fun x => hclsub (hs x)

/-- A continuous dense-range image inherits a dense subset of cardinality
strictly below the continuum. -/
theorem exists_dense_cardinalMk_lt_continuum_of_continuous_denseRange
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hfrange : DenseRange f)
    (s : Set X) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ t : Set Y, Dense t ∧ #t < Cardinal.continuum := by
  let g : s → Y := fun x => f x
  refine ⟨Set.range g, denseRange_restrict_of_continuous f hf hfrange s hs, ?_⟩
  have hle : Cardinal.lift.{u} (#(Set.range g)) ≤ Cardinal.lift.{v} (#s) :=
    Cardinal.mk_range_le_lift
  have hsmall : Cardinal.lift.{v} (#s) < Cardinal.continuum := by
    exact Cardinal.lift_lt_continuum.mpr hcard
  exact Cardinal.lift_lt_continuum.mp (hle.trans_lt hsmall)

end MathlibAnnex.Topology
