/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.AmplifiedOrbit
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic

/-!
# Full weak-operator density for a finite inequivalent family

The finite product of the actual `ContinuousLinearMapWOT` spaces is the
operator-topology realization of the finite direct-sum algebra. Arbitrary
finite vector tests, including repeated copies of each representation,
first give pointwise norm approximation. Continuity of the scalar test
functionals and the actual inducing maps then give full product-WOT density.
No density of the unit ball, self-adjoint density, or norm-controlled exact
interpolation is asserted here. No claim about irreducibility of the sum is
made. The two-representation case is obtained by a two-element index type.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Topology

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

private theorem exists_pos_le_on_finset {D : Type*} (s : Finset D) :
    ∀ r : D → ℝ, (∀ i ∈ s, 0 < r i) → ∃ d > 0, ∀ i ∈ s, d ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r _
    exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    intro r hr
    obtain ⟨d, hd, hds⟩ := ih r (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min (r i) d, lt_min (hr i (Finset.mem_insert_self i s)) hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hds j hj)

/-- A finite-test criterion for pointwise closure, with no topology on the
parameter type. This private adapter is applied to the proved finite-vector
approximation theorem below, not postulated for a representation. -/
private theorem mem_closure_range_of_finite_approximation
    {D X : Type*} {E : D → Type*} [∀ i, PseudoMetricSpace (E i)]
    (f : X → ∀ i, E i) (g : ∀ i, E i)
    (h : ∀ s : Finset D, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ x : X, ∀ i ∈ s, dist (f x i) (g i) < epsilon) :
    g ∈ closure (Set.range f) := by
  classical
  apply _root_.mem_closure_iff.mpr
  intro U hU hg
  obtain ⟨s, V, hV, hVU⟩ := isOpen_pi_iff.mp hU g hg
  have hballs : ∀ i : s, ∃ r > 0, ball (g i.1) r ⊆ V i.1 := by
    intro i
    exact Metric.isOpen_iff.mp (hV i.1 i.2).1 (g i.1) (hV i.1 i.2).2
  choose r hr hball using hballs
  obtain ⟨d, hd, hds⟩ := exists_pos_le_on_finset (Finset.univ : Finset s) r
    (fun i _ => hr i)
  obtain ⟨x, hx⟩ := h s d hd
  refine ⟨f x, hVU ?_, ⟨x, rfl⟩⟩
  intro i hi
  apply hball ⟨i, hi⟩
  exact (hx i hi).trans_le (hds ⟨i, hi⟩ (Finset.mem_univ _))

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- The original-algebra diagonal image is dense in the finite product of
all bounded-operator spaces equipped with their genuine weak-operator
topologies. The Hilbert-space dimensions and densities are unrestricted. -/
theorem denseRange_pi_wot_of_pairwise_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j)) :
    DenseRange (fun a : A => fun i => ContinuousLinearMapWOT.ofCLM (pi i a)) := by
  classical
  intro T
  let R : A → (∀ q : Sigma H, H q.1) := fun a q => pi q.1 a q.2
  let t : ∀ q : Sigma H, H q.1 := fun q => T q.1 q.2
  have ht : t ∈ closure (Set.range R) := by
    apply mem_closure_range_of_finite_approximation R t
    intro s epsilon hepsilon
    let x : ∀ i, s → H i := fun i q =>
      if hqi : q.1.1 = i then hqi ▸ q.1.2 else 0
    obtain ⟨a, ha⟩ := exists_forall_apply_sub_norm_lt_of_finite_vector_tests
      (J := fun _ : I => s) pi hirr hne x (fun i => (T i).toCLM) hepsilon
    refine ⟨a, fun q hq => ?_⟩
    have hq' := ha q.1 ⟨q, hq⟩
    simpa [x, R, t, dist_eq_norm] using hq'
  let W : A → (∀ i, H i →WOT[ℂ] H i) :=
    fun a i => ContinuousLinearMapWOT.ofCLM (pi i a)
  let e : (∀ i, H i →WOT[ℂ] H i) →
      (∀ i, (H i × StrongDual ℂ (H i)) → ℂ) :=
    fun z i q => q.2 (z i q.1)
  have he : IsInducing e := by
    exact Topology.IsInducing.piMap (fun i =>
      ContinuousLinearMapWOT.isInducing_inducingFn
        (σ := RingHom.id ℂ) (E := H i) (F := H i))
  let E : (∀ q : Sigma H, H q.1) →
      (∀ i, (H i × StrongDual ℂ (H i)) → ℂ) :=
    fun z i q => q.2 (z ⟨i, q.1⟩)
  have hE : Continuous E :=
    continuous_pi (fun i => continuous_pi (fun q =>
      q.2.continuous.comp (continuous_apply (⟨i, q.1⟩ : Sigma H))))
  have hmap : Set.MapsTo E (Set.range R) (e '' Set.range W) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨W a, ⟨a, rfl⟩, rfl⟩
  have himage : e T ∈ closure (e '' Set.range W) := hmap.closure hE ht
  change T ∈ closure (Set.range W)
  rw [he.closure_eq_preimage_closure_image]
  exact himage

/-- Full closure equality, not merely one-vector density or density of each
individual coordinate projection. This equality concerns the whole algebra
image, not its closed unit ball. -/
theorem closure_range_pi_wot_eq_univ_of_pairwise_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j)) :
    closure (Set.range (fun a : A => fun i => ContinuousLinearMapWOT.ofCLM (pi i a))) =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  exact denseRange_pi_wot_of_pairwise_not_unitaryEquivalent pi hirr hne

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
