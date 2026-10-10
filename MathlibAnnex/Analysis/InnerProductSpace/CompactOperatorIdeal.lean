/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.OperatorIdeal
import MathlibAnnex.Analysis.Normed.Operator.CompactIdeal
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Compact operators and the least nonzero closed operator ideal

`compactOperatorIdeal` bundles the existing `IsCompactOperator` predicate as a
`TwoSidedIdeal` of the original normed bounded-operator ring. Its carrier is also
Mathlib's existing `compactOperator` submodule; no new compactness predicate is used.

The finite-rank approximation below is proved directly: a finite net for the image
of the unit ball spans a finite-dimensional target subspace, and orthogonal projection
onto that subspace gives operator-norm approximation. No separability or global basis
assumption, spectral cutoff, or classification of closed ideals is used.
-/

set_option autoImplicit false
noncomputable section
open Set Metric


namespace InnerProductSpace

variable {𝕜 E H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Rank-one operators are compact, also when one of the two vectors is zero.
Neither ambient space needs to be complete. -/
theorem isCompactOperator_rankOne (u : E) (v : H) :
    IsCompactOperator (rankOne 𝕜 u v) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 v)).clm_comp
    (ContinuousLinearMap.toSpanSingleton 𝕜 u)

end InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Nonzero Hilbert spaces have a nonzero compact-operator ideal. -/
theorem compactOperatorIdeal_ne_bot [Nontrivial H] :
    compactOperatorIdeal 𝕜 H ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  intro heq
  have hm : InnerProductSpace.rankOne 𝕜 x x ∈ compactOperatorIdeal 𝕜 H :=
    (mem_compactOperatorIdeal _).2 (InnerProductSpace.isCompactOperator_rankOne x x)
  rw [heq, TwoSidedIdeal.mem_bot] at hm
  exact InnerProductSpace.rankOne_ne_zero hx hx hm

/-- On the zero Hilbert space the compact ideal is the zero ideal (and also top). -/
theorem compactOperatorIdeal_eq_bot_of_subsingleton [Subsingleton H] :
    compactOperatorIdeal 𝕜 H = ⊥ := by
  apply bot_unique
  intro T _
  rw [TwoSidedIdeal.mem_bot]
  ext x
  exact Subsingleton.elim _ _

end ContinuousLinearMap

namespace IsCompactOperator

variable {𝕜 E H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Compact operators with Hilbert target admit finite-rank approximation in the original
operator norm. The domain need not be complete or an inner-product space. -/
theorem exists_finiteDimensional_range_norm_sub_lt {T : E →L[𝕜] H}
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : E →L[𝕜] H,
      FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧ ‖T - F‖ < ε := by
  classical
  obtain ⟨C, hC, hTC⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨s, hs, hcover⟩ :=
    (Metric.totallyBounded_iff.1 hC.totallyBounded) (ε / 2) (half_pos hε)
  let M : Submodule 𝕜 H := Submodule.span 𝕜 s
  letI : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜 hs
  letI : CompleteSpace M := FiniteDimensional.complete 𝕜 M
  let F : E →L[𝕜] H := M.starProjection.comp T
  have hFM : LinearMap.range F.toLinearMap ≤ M := by
    rintro y ⟨x, rfl⟩
    exact (M.orthogonalProjectionOnto (T x)).property
  have hF : FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) :=
    Submodule.finiteDimensional_of_le hFM
  have hball : ∀ x ∈ closedBall (0 : E) 1, ‖(T - F) x‖ ≤ ε / 2 := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover (hTC ⟨x, hx, rfl⟩))
    have hym : y ∈ M := Submodule.subset_span hy
    calc
      ‖(T - F) x‖ = ‖T x - M.starProjection (T x)‖ := rfl
      _ = ⨅ z : M, ‖T x - (z : H)‖ := Submodule.starProjection_minimal (T x)
      _ ≤ ‖T x - y‖ := ciInf_le (f := fun z : M => ‖T x - (z : H)‖)
        ⟨(0 : ℝ), by rintro _ ⟨z, rfl⟩; exact norm_nonneg (T x - (z : H))⟩
        (⟨y, hym⟩ : M)
      _ ≤ ε / 2 := (show ‖T x - y‖ < ε / 2 by
        have hdist := mem_ball.mp hxy
        change dist (T x) y < ε / 2 at hdist
        simpa only [dist_eq_norm] using hdist).le
  have hnorm : ‖T - F‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let z : E := ((‖x‖ : 𝕜)⁻¹) • x
    have hz : ‖z‖ = 1 := by
      simp [z, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hn, hn.ne']
    have h := hball z (by simpa only [mem_closedBall, dist_zero_right, hz] using
      (le_refl (1 : ℝ)))
    have he : ‖(T - F) z‖ = ‖(T - F) x‖ / ‖x‖ := by
      simp only [z, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos hn, div_eq_mul_inv, mul_comm]
    rw [he] at h
    exact (div_le_iff₀ hn).1 h
  exact ⟨F, hF, hnorm.trans_lt (half_lt_self hε)⟩

/-- The previous approximation is a closure statement, not merely pointwise convergence. -/
theorem mem_closure_setOf_finiteDimensional_range {T : E →L[𝕜] H}
    (hT : IsCompactOperator T) :
    T ∈ closure {F : E →L[𝕜] H | FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap)} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨F, hF, hdist⟩ := hT.exists_finiteDimensional_range_norm_sub_lt hε
  exact ⟨F, hF, by simpa only [dist_eq_norm, norm_sub_rev] using hdist⟩

end IsCompactOperator

namespace ContinuousLinearMap

variable {𝕜 E H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- For Hilbert targets the finite-rank operators have exactly the compact operators as
operator-norm closure. No approximation property is postulated. -/
theorem closure_setOf_finiteDimensional_range :
    closure {F : E →L[𝕜] H | FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap)} =
      {T : E →L[𝕜] H | IsCompactOperator T} := by
  apply subset_antisymm
  · apply closure_minimal _ isClosed_setOf_isCompactOperator
    intro F hF
    letI : FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) := hF
    exact F.isCompactOperator_of_finiteDimensional_range
  · intro T hT
    exact hT.mem_closure_setOf_finiteDimensional_range

end ContinuousLinearMap

namespace TwoSidedIdeal

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Every nonzero norm-closed two-sided ideal of B(H) contains every compact operator. -/
theorem mem_of_isCompactOperator (I : TwoSidedIdeal (H →L[𝕜] H))
    (hI : I ≠ ⊥) (hclosed : IsClosed (I : Set (H →L[𝕜] H)))
    {T : H →L[𝕜] H} (hT : IsCompactOperator T) : T ∈ I := by
  apply closure_minimal (t := (I : Set (H →L[𝕜] H))) _ hclosed
    hT.mem_closure_setOf_finiteDimensional_range
  intro F hF
  letI : FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) := hF
  exact I.mem_of_finiteDimensional_range hI F

/-- A bundled ideal inclusion, with the zero ideal excluded explicitly. -/
theorem compactOperatorIdeal_le (I : TwoSidedIdeal (H →L[𝕜] H))
    (hI : I ≠ ⊥) (hclosed : IsClosed (I : Set (H →L[𝕜] H))) :
    ContinuousLinearMap.compactOperatorIdeal 𝕜 H ≤ I := by
  intro T hT
  exact I.mem_of_isCompactOperator hI hclosed
    ((ContinuousLinearMap.mem_compactOperatorIdeal T).1 hT)

/-- The zero branch must not be erased when discussing all closed operator ideals. -/
theorem eq_bot_or_compactOperatorIdeal_le (I : TwoSidedIdeal (H →L[𝕜] H))
    (hclosed : IsClosed (I : Set (H →L[𝕜] H))) :
    I = ⊥ ∨ ContinuousLinearMap.compactOperatorIdeal 𝕜 H ≤ I := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · exact Or.inr (I.compactOperatorIdeal_le hI hclosed)

end TwoSidedIdeal
