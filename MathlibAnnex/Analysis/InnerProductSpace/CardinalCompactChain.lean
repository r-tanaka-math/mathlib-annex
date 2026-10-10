/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.ClosedSubspaceCardinality
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactRange
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisRangeCardinality
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorIdeal
import MathlibAnnex.Analysis.Normed.Operator.CardinalCompact

/-!
# The strict chain of cardinal-compact operator ideals

For a closed Hilbert subspace `M`, the orthogonal projection onto `M` is
cardinal-compact at `α` exactly when the Hilbert-basis cardinality of `M` is
strictly smaller than `α`. Prescribed closed subspaces therefore separate two
thresholds in the genuine interval from `ℵ₀` to the successor of the ambient
Hilbert dimension.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped Cardinal Topology

universe uF uH uI uA

namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [hH : CompleteSpace H]

include hH in
/-- Orthogonal projection is cardinal-compact exactly below the Hilbert
cardinality of its closed range. -/
theorem isCardinalCompactOperator_starProjection_iff
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    {ι : Type uI} (b : HilbertBasis ι 𝕜 M)
    {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α M.starProjection ↔
      Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α := by
  letI : CompleteSpace M := hM.completeSpace_coe
  constructor
  · intro hP
    apply M.starProjection.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator
      hP M hM
    · simpa only [Submodule.range_starProjection] using (le_refl M)
    · exact b
  · intro hb
    apply (isCardinalCompactOperator_iff_image_closedBall
      (α := α) M.starProjection.toLinearMap).mpr
    have hball : Metric.CardinalTotallyBounded α
        (Metric.closedBall (0 : M) 1) :=
      b.cardinalTotallyBounded_of_isBounded hα hb isBounded_closedBall
    have himage := hball.image (f := M.subtypeL) M.subtypeL.uniformContinuous
    apply himage.subset
    rintro y ⟨x, hx, rfl⟩
    refine ⟨M.orthogonalProjectionOnto x, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (M.norm_orthogonalProjectionOnto_apply_le x).trans
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

include hH in
/-- Ideal membership of an orthogonal projection is the same strict Hilbert
cardinality inequality. -/
theorem starProjection_mem_cardinalCompactOperatorIdeal_iff
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    {ι : Type uI} (b : HilbertBasis ι 𝕜 M)
    {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    M.starProjection ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα ↔
      Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α := by
  rw [mem_cardinalCompactOperatorIdeal]
  exact isCardinalCompactOperator_starProjection_iff M hM b hα

/-- The aleph-zero endpoint is the existing compact-operator ideal. -/
theorem cardinalCompactOperatorIdeal_aleph0_eq_compactOperatorIdeal :
    cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H)
      (Cardinal.aleph0 : Cardinal.{uH}) le_rfl = compactOperatorIdeal 𝕜 H :=
  cardinalCompactOperatorIdeal_aleph0_eq

/-- On a nonzero Hilbert space the first ideal in the chain is nonzero. -/
theorem cardinalCompactOperatorIdeal_aleph0_ne_bot [Nontrivial H] :
    cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H)
      (Cardinal.aleph0 : Cardinal.{uH}) le_rfl ≠ ⊥ := by
  rw [cardinalCompactOperatorIdeal_aleph0_eq_compactOperatorIdeal]
  exact compactOperatorIdeal_ne_bot

include hH in
/-- At the successor of an actual infinite Hilbert-basis cardinal, every
bounded operator is cardinal-compact. -/
theorem cardinalCompactOperatorIdeal_succ_mk_eq_top_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℝ H)
    (hι : Cardinal.aleph0 ≤ #ι) :
    cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) (Order.succ (#ι))
      (hι.trans (Order.le_succ _)) = ⊤ := by
  apply top_unique
  intro T _
  rw [mem_cardinalCompactOperatorIdeal]
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_real
    (hι.trans (Order.le_succ _))).mpr
  intro M hM hMT κ c
  letI : CompleteSpace M := hM.completeSpace_coe
  have hq : Surjective M.orthogonalProjectionOnto := by
    intro x
    exact ⟨x, M.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  have hc := b.lift_mk_le_of_denseRange c M.orthogonalProjectionOnto hq.denseRange
  have hc' : #κ ≤ #ι := by simpa only [Cardinal.lift_id] using hc
  simpa only [Cardinal.lift_id] using hc'.trans_lt (Order.lt_succ (#ι))

include hH in
/-- Complex counterpart of the top endpoint. -/
theorem cardinalCompactOperatorIdeal_succ_mk_eq_top_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℂ H)
    (hι : Cardinal.aleph0 ≤ #ι) :
    cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) (Order.succ (#ι))
      (hι.trans (Order.le_succ _)) = ⊤ := by
  apply top_unique
  intro T _
  rw [mem_cardinalCompactOperatorIdeal]
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_complex
    (hι.trans (Order.le_succ _))).mpr
  intro M hM hMT κ c
  letI : CompleteSpace M := hM.completeSpace_coe
  have hq : Surjective M.orthogonalProjectionOnto := by
    intro x
    exact ⟨x, M.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  have hc := b.lift_mk_le_of_denseRange c M.orthogonalProjectionOnto hq.denseRange
  have hc' : #κ ≤ #ι := by simpa only [Cardinal.lift_id] using hc
  simpa only [Cardinal.lift_id] using hc'.trans_lt (Order.lt_succ (#ι))

include hH in
/-- Strict inclusion of the actual real cardinal-compact ideals throughout the
valid threshold interval. -/
theorem cardinalCompactOperatorIdeal_lt_of_lt_of_le_succ_mk_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℝ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β) (hαβ : α < β)
    (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα <
      cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) β hβ := by
  have hακ : α ≤ #ι := Order.lt_succ_iff.mp (hαβ.trans_le hβκ)
  obtain ⟨M, hM, w, c, hw⟩ :=
    b.exists_closed_submodule_hilbertBasis_mk_eq_of_le α hακ
  have hle := cardinalCompactOperatorIdeal_mono (𝕜 := ℝ) (E := H)
    hα hβ hαβ.le
  apply lt_of_le_of_ne hle
  intro heq
  have hmemβ : M.starProjection ∈
      cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) β hβ :=
    (starProjection_mem_cardinalCompactOperatorIdeal_iff M hM c hβ).mpr
      (by simpa only [Cardinal.lift_id, hw] using hαβ)
  have hmemα : M.starProjection ∈
      cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα := by
    rw [heq]
    exact hmemβ
  have hlt := (starProjection_mem_cardinalCompactOperatorIdeal_iff M hM c hα).mp hmemα
  have haa : α < α := by
    simpa only [Cardinal.lift_id, hw] using hlt
  exact (lt_irrefl α haa)

include hH in
/-- Strict inclusion of the actual complex cardinal-compact ideals throughout
the valid threshold interval. -/
theorem cardinalCompactOperatorIdeal_lt_of_lt_of_le_succ_mk_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℂ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β) (hαβ : α < β)
    (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα <
      cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) β hβ := by
  have hακ : α ≤ #ι := Order.lt_succ_iff.mp (hαβ.trans_le hβκ)
  obtain ⟨M, hM, w, c, hw⟩ :=
    b.exists_closed_submodule_hilbertBasis_mk_eq_of_le α hακ
  have hle := cardinalCompactOperatorIdeal_mono (𝕜 := ℂ) (E := H)
    hα hβ hαβ.le
  apply lt_of_le_of_ne hle
  intro heq
  have hmemβ : M.starProjection ∈
      cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) β hβ :=
    (starProjection_mem_cardinalCompactOperatorIdeal_iff M hM c hβ).mpr
      (by simpa only [Cardinal.lift_id, hw] using hαβ)
  have hmemα : M.starProjection ∈
      cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα := by
    rw [heq]
    exact hmemβ
  have hlt := (starProjection_mem_cardinalCompactOperatorIdeal_iff M hM c hα).mp hmemα
  have haa : α < α := by
    simpa only [Cardinal.lift_id, hw] using hlt
  exact (lt_irrefl α haa)

end ContinuousLinearMap
