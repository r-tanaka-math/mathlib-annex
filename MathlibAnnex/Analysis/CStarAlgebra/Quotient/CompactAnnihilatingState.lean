/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import MathlibAnnex.Analysis.InnerProductSpace.CompactEscape

/-!
# A singular state detecting a specified noncompact operator

The index set is ALL finite-dimensional algebraic subspaces, ordered by inclusion.
No sequence, separability or countable Hilbert basis is used. Noncompactness gives
unit vectors outside each such subspace with a uniform positive lower bound.
Compact operators tend to zero on these vectors by operator-norm finite-rank
approximation. A weak-star cluster point of the actual vector states annihilates
the compact preimage ideal and retains a strictly positive value on `a⋆a`.

The unitization action is the existing `NonUnitalCStarRepresentation.unitization`.
It need not be faithful. The positive value on the original algebra is the extra
condition which excludes the character at infinity. No C-star quotient, pure-state
existence, or positivity of the earlier Hahn--Banach separator is assumed here.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual vector states on the unitization are normalized positive functionals
in the existing weak-star state space. No faithfulness of the action is required. -/
theorem vectorFunctional_unitization_mem_weakStateSpace
    (pi : NonUnitalCStarRepresentation A H) {x : H} (hx : ‖x‖ = 1) :
    StrongDual.toWeakDual (Representation.vectorFunctional pi.unitization x) ∈
      weakStateSpace (Unitization ℂ A) := by
  exact ⟨fun a ha => Representation.vectorFunctional_nonnegative pi.unitization x ha,
    Representation.vectorFunctional_one pi.unitization hx⟩

/-- The detecting value belongs to the original algebra and is the exact squared
norm of its action, not just a lower estimate on a linear separator. -/
theorem vectorFunctional_unitization_star_inr_mul_inr
    (pi : NonUnitalCStarRepresentation A H) (x : H) (a : A) :
    Representation.vectorFunctional pi.unitization x
      (star (Unitization.inr a) * Unitization.inr a) = (‖pi a x‖ ^ 2 : ℝ) := by
  rw [Representation.vectorFunctional_star_mul,
    NonUnitalCStarRepresentation.unitization_inr, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Every specified noncompact image admits a genuine weak-star state on the
unitization, annihilating the compact preimage ideal and strictly positive on
its square. The lower bound prevents degeneration to the infinity character. -/
theorem exists_weakState_annihilating_compacts_of_not_isCompactOperator
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : ¬ IsCompactOperator (pi a)) :
    ∃ psi : WeakDual ℂ (Unitization ℂ A),
      psi ∈ weakStateFace
        (MathlibAnnex.CStarAlgebra.compactPreimageIdeal
          pi.unitization.toNonUnitalStarAlgHom) ∧
      (Metric.infDist (pi a)
        (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H))) ^ 2 / 4 ≤
          (psi (star (Unitization.inr a) * Unitization.inr a)).re ∧
      0 < (psi (star (Unitization.inr a) * Unitization.inr a)).re := by
  classical
  let D := Unitization ℂ A
  let J := MathlibAnnex.CStarAlgebra.compactPreimageIdeal
    pi.unitization.toNonUnitalStarAlgHom
  let d : ℝ := Metric.infDist (pi a)
    (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H))
  have hd : 0 < d := ContinuousLinearMap.infDist_compactOperator_pos ha
  let b : D := star (Unitization.inr a) * Unitization.inr a
  let iota := {M : Submodule ℂ H // FiniteDimensional ℂ M}
  letI : Nonempty iota := ⟨⟨⊥, inferInstance⟩⟩
  letI : IsDirectedOrder iota := by
    refine ⟨?_⟩
    intro M N
    letI : FiniteDimensional ℂ M.val := M.property
    letI : FiniteDimensional ℂ N.val := N.property
    refine ⟨⟨M.val ⊔ N.val, inferInstance⟩, ?_, ?_⟩
    · change M.val ≤ M.val ⊔ N.val
      exact le_sup_left
    · change N.val ≤ M.val ⊔ N.val
      exact le_sup_right
  have hex (M : iota) : ∃ x : H, x ∈ M.valᗮ ∧ ‖x‖ = 1 ∧ d / 2 < ‖pi a x‖ := by
    letI : FiniteDimensional ℂ M.val := M.property
    exact ContinuousLinearMap.exists_norm_eq_one_mem_orthogonal_norm_apply_gt_infDist
      (pi a) ha M.val
  choose x hxm hxn hxa using hex
  let psi : iota → WeakDual ℂ D := fun M =>
    StrongDual.toWeakDual (Representation.vectorFunctional pi.unitization (x M))
  have hstate (M : iota) : psi M ∈ weakStateSpace D :=
    vectorFunctional_unitization_mem_weakStateSpace pi (hxn M)
  have hvalue (M : iota) : d ^ 2 / 4 ≤ (psi M b).re := by
    have hv : (psi M b).re = ‖pi a (x M)‖ ^ 2 := by
      change (Representation.vectorFunctional pi.unitization (x M)
        (star (Unitization.inr a) * Unitization.inr a)).re = ‖pi a (x M)‖ ^ 2
      rw [vectorFunctional_unitization_star_inr_mul_inr, Complex.ofReal_re]
    rw [hv]
    have hsquare : (d / 2) ^ 2 < ‖pi a (x M)‖ ^ 2 :=
      (sq_lt_sq₀ (by positivity : 0 ≤ d / 2) (norm_nonneg _)).2 (hxa M)
    nlinarith
  have hlim (j : D) (hj : j ∈ J) :
      Tendsto (fun M => psi M j) atTop (𝓝 0) := by
    have hc : IsCompactOperator (pi.unitization j) :=
      (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
        pi.unitization.toNonUnitalStarAlgHom j).1 hj
    have ht := ContinuousLinearMap.tendsto_apply_zero_of_isCompactOperator_of_mem_orthogonal
      (pi.unitization j) hc x hxm (fun M => (hxn M).le)
    rw [Metric.tendsto_nhds] at ht ⊢
    intro ε hε
    filter_upwards [ht ε hε] with M hM
    change dist (pi.unitization j (x M)) 0 < ε at hM
    rw [dist_zero_right] at hM ⊢
    change ‖inner ℂ (x M) (pi.unitization j (x M))‖ < ε
    have hn := norm_inner_le_norm (𝕜 := ℂ) (x M) (pi.unitization j (x M))
    rw [hxn M, one_mul] at hn
    exact hn.trans_lt hM
  have hfaceBot : weakStateFace (⊥ : TwoSidedIdeal D) = weakStateSpace D := by
    ext p
    constructor
    · exact fun hp => hp.1
    · intro hp
      refine ⟨hp, ?_⟩
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      rw [hj0, map_zero]
  have hcompact : IsCompact (weakStateSpace D) := by
    rw [← hfaceBot]
    exact isCompact_weakStateFace (⊥ : TwoSidedIdeal D)
  have hmap : Filter.map psi atTop ≤ 𝓟 (weakStateSpace D) :=
    Filter.tendsto_principal.2 (Filter.Eventually.of_forall hstate)
  obtain ⟨phi, hphi, hcluster⟩ := hcompact.exists_mapClusterPt hmap
  have hcp : ClusterPt phi (Filter.map psi atTop) := hcluster
  have hann (j : D) (hj : j ∈ J) : phi j = 0 := by
    letI : NeBot (𝓝 phi ⊓ Filter.map psi atTop) := hcp
    have hzero : Tendsto (fun p : WeakDual ℂ D => p j)
        (Filter.map psi atTop) (𝓝 0) := by
      change Filter.map (fun p : WeakDual ℂ D => p j) (Filter.map psi atTop) ≤ 𝓝 0
      rw [Filter.map_map]
      exact hlim j hj
    exact tendsto_nhds_unique
      (((WeakDual.eval_continuous j).tendsto phi).mono_left inf_le_left)
      (hzero.mono_left inf_le_right)
  have hclosed : IsClosed {p : WeakDual ℂ D | d ^ 2 / 4 ≤ (p b).re} :=
    isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous b))
  have hmapValue : Filter.map psi atTop ≤
      𝓟 {p : WeakDual ℂ D | d ^ 2 / 4 ≤ (p b).re} :=
    Filter.tendsto_principal.2 (Filter.Eventually.of_forall hvalue)
  have hbound : d ^ 2 / 4 ≤ (phi b).re :=
    hclosed.mem_of_nhdsWithin_neBot (hcp.mono hmapValue)
  refine ⟨phi, ⟨hphi, hann⟩, hbound, ?_⟩
  exact lt_of_lt_of_le (by positivity : 0 < d ^ 2 / 4) hbound

end MathlibAnnex.Analysis.CStarAlgebra
