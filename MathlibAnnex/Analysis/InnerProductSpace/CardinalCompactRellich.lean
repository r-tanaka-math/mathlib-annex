/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactAdjoint
import MathlibAnnex.Analysis.InnerProductSpace.ClosedSubmoduleImage
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactRange
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Rellich's criterion for cardinal-compact Hilbert-space operators

The small space is a closed submodule of the source, measured by the indices of
an actual Hilbert basis. The forward implication uses the supplied two-threshold
cutoff, its closed literal image, a genuine continuous linear equivalence onto
that image, and the Hilbert-basis cardinality theorem. The inverse estimate is
proved explicitly. No closedness of the full operator range is assumed.

The reverse implication uses one bounded projected image and one small
orthogonal residual at each radius. No countable union of small sets is taken.
The large-subspace formulation uses the orthogonal complement, not subtraction
of infinite cardinals. Real and complex endpoints have no cutoff premise.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped Cardinal Topology

universe uF uH uK uI uA
namespace ContinuousLinearMap

section ImageEquivalence

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

include hH hK in
/-- Cardinal compactness controls every Hilbert basis of a closed source
subspace on which the operator is bounded below. The basis index is arbitrary. -/
theorem hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator_of_lower_bound
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hT : IsCardinalCompactOperator α T)
    (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    (hTS : IsClosed (T '' (S : Set H))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 S) :
    Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α := by
  let M : Submodule 𝕜 K := S.map T.toLinearMap
  have hM : IsClosed (M : Set K) := hTS
  letI : CompleteSpace M := hM.completeSpace_coe
  have hMT : M ≤ T.range := by
    rintro y ⟨x, hxS, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 M
  have hc := T.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator hT M hM hMT c
  let e : S ≃L[𝕜] M := T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower
  have heq := b.lift_mk_eq_of_continuous_linear_equiv c e
  have heq' := congrArg (fun q => Cardinal.lift.{uA} q) heq
  have hc' : Cardinal.lift.{uI} (Cardinal.lift.{uA} (#w)) <
      Cardinal.lift.{uI} (Cardinal.lift.{uK} α) := Cardinal.lift_lt.mpr hc
  simp only [Cardinal.lift_lift] at heq' hc'
  have hcommon : Cardinal.lift.{uK} (Cardinal.lift.{uA} (#ι)) <
      Cardinal.lift.{uK} (Cardinal.lift.{uI} α) := by
    simpa only [Cardinal.lift_lift] using heq'.trans_lt hc'
  exact Cardinal.lift_lt.mp hcommon

end ImageEquivalence

section Approximation

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

include hH in
/-- Small source subspaces and arbitrarily small orthogonal restriction norms
imply cardinal compactness. The target need not be Hilbert or complete. -/
theorem isCardinalCompactOperator_of_forall_small_submodule
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ M : Submodule 𝕜 H, IsClosed (M : Set H) ∧
      ∃ (ι : Type uH) (b : HilbertBasis ι 𝕜 M),
        Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧
          ‖T.comp Mᗮ.subtypeL‖ < ε) : IsCardinalCompactOperator α T := by
  classical
  apply (isCardinalCompactOperator_iff_image_closedBall (α := α) T.toLinearMap).mpr
  apply Metric.cardinalTotallyBounded_image_of_uniform_approximation
    (α := α) (s := Metric.closedBall (0 : H) 1) (f := T)
  intro η hη
  obtain ⟨M, hM, ι, b, hb, hrest⟩ := hsmall η hη
  letI : CompleteSpace M := hM.completeSpace_coe
  let p : H →L[𝕜] M := M.orthogonalProjectionOnto
  let q : M →L[𝕜] K := T.comp M.subtypeL
  let g : H →L[𝕜] K := q.comp p
  have hp : Bornology.IsBounded (p '' Metric.closedBall (0 : H) 1) :=
    p.lipschitz.isBounded_image isBounded_closedBall
  have hn := (b.cardinalTotallyBounded_of_isBounded hα hb hp).image q.uniformContinuous
  have heq : q '' (p '' Metric.closedBall (0 : H) 1) =
      g '' Metric.closedBall (0 : H) 1 := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨p x, ⟨x, hx, rfl⟩, rfl⟩
  rw [heq] at hn
  refine ⟨g, hn, ?_⟩
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hr : x - M.starProjection x ∈ Mᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hrnorm : ‖x - M.starProjection x‖ ≤ ‖x‖ := by
    simpa only [Submodule.starProjection_orthogonal_val] using
      Mᗮ.norm_starProjection_apply_le x
  have hval : g x = T (M.starProjection x) := rfl
  calc
    dist (T x) (g x) = ‖T (x - M.starProjection x)‖ := by
      rw [hval, dist_eq_norm, map_sub]
    _ = ‖(T.comp Mᗮ.subtypeL) ⟨x - M.starProjection x, hr⟩‖ := rfl
    _ ≤ ‖T.comp Mᗮ.subtypeL‖ * ‖x - M.starProjection x‖ :=
      (T.comp Mᗮ.subtypeL).le_opNorm _
    _ ≤ ‖T.comp Mᗮ.subtypeL‖ := by
      nlinarith [norm_nonneg (T.comp Mᗮ.subtypeL)]
    _ ≤ η := hrest.le

include hH in
/-- Rellich's small-space and large-space formulations are the same by
orthogonal decomposition. The codimension is measured on `Nᗮ`, not by
subtracting infinite cardinals. -/
theorem forall_small_submodule_iff_forall_small_orthogonal
    (T : H →L[𝕜] K) (α : Cardinal.{uA}) :
    (∀ ε : ℝ, 0 < ε → ∃ M : Submodule 𝕜 H, IsClosed (M : Set H) ∧
      ∃ (ι : Type uH) (b : HilbertBasis ι 𝕜 M),
        Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp Mᗮ.subtypeL‖ < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ N : Submodule 𝕜 H, IsClosed (N : Set H) ∧
      ∃ (ι : Type uH) (b : HilbertBasis ι 𝕜 Nᗮ),
        Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp N.subtypeL‖ < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨M, hM, ι, b, hb, hn⟩ := h ε hε
    letI : CompleteSpace M := hM.completeSpace_coe
    refine ⟨Mᗮ, M.isClosed_orthogonal, ?_⟩
    rw [Submodule.orthogonal_orthogonal]
    exact ⟨ι, b, hb, hn⟩
  · intro h ε hε
    obtain ⟨N, hN, ι, b, hb, hn⟩ := h ε hε
    letI : CompleteSpace N := hN.completeSpace_coe
    refine ⟨Nᗮ, N.isClosed_orthogonal, ι, b, hb, ?_⟩
    rw [Submodule.orthogonal_orthogonal]
    exact hn

end Approximation

section RealComplex

variable {H : Type uH} [NormedAddCommGroup H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [hK : CompleteSpace K]

include hH hK in
/-- The real Rellich criterion, with the actual real two-threshold cutoff applied.
The small space may be zero. The operator need not have closed range. -/
theorem isCardinalCompactOperator_iff_rellich_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (T : H →L[ℝ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : Submodule ℝ H, IsClosed (M : Set H) ∧
        ∃ (ι : Type uH) (b : HilbertBasis ι ℝ M),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp Mᗮ.subtypeL‖ < ε := by
  constructor
  · intro hT ε hε
    obtain ⟨M, hM, hlower, -, hrest, him⟩ :=
      T.exists_closed_submodule_two_threshold_cutoff_real hε
    letI : CompleteSpace M := hM.completeSpace_coe
    obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ M
    exact ⟨M, hM, w, b,
      T.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator_of_lower_bound
        hT M hM him (half_pos hε) hlower b, hrest⟩
  · exact fun h => T.isCardinalCompactOperator_of_forall_small_submodule hα h

include hH hK in
/-- The complex Rellich criterion, using the supplied complex cutoff rather than
any strict same-threshold spectral assertion. -/
theorem isCardinalCompactOperator_iff_rellich_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : Submodule ℂ H, IsClosed (M : Set H) ∧
        ∃ (ι : Type uH) (b : HilbertBasis ι ℂ M),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp Mᗮ.subtypeL‖ < ε := by
  constructor
  · intro hT ε hε
    obtain ⟨M, hM, hlower, -, hrest, him⟩ :=
      T.exists_closed_submodule_two_threshold_cutoff_complex hε
    letI : CompleteSpace M := hM.completeSpace_coe
    obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ M
    exact ⟨M, hM, w, b,
      T.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator_of_lower_bound
        hT M hM him (half_pos hε) hlower b, hrest⟩
  · exact fun h => T.isCardinalCompactOperator_of_forall_small_submodule hα h

include hH hK in
/-- The real large-subspace/codimension version of Rellich's criterion. -/
theorem isCardinalCompactOperator_iff_rellich_orthogonal_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (T : H →L[ℝ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : Submodule ℝ H, IsClosed (N : Set H) ∧
        ∃ (ι : Type uH) (b : HilbertBasis ι ℝ Nᗮ),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp N.subtypeL‖ < ε :=
  (T.isCardinalCompactOperator_iff_rellich_real hα).trans
    (T.forall_small_submodule_iff_forall_small_orthogonal α)

include hH hK in
/-- The complex large-subspace/codimension version, with the same original operator. -/
theorem isCardinalCompactOperator_iff_rellich_orthogonal_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : Submodule ℂ H, IsClosed (N : Set H) ∧
        ∃ (ι : Type uH) (b : HilbertBasis ι ℂ Nᗮ),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uH} α ∧ ‖T.comp N.subtypeL‖ < ε :=
  (T.isCardinalCompactOperator_iff_rellich_complex hα).trans
    (T.forall_small_submodule_iff_forall_small_orthogonal α)

end RealComplex
end ContinuousLinearMap
