/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactChain
import MathlibAnnex.Analysis.InnerProductSpace.ClosedOperatorIdealClassification

/-!
# Threshold uniqueness for closed operator ideals

On an infinite real or complex Hilbert space, cardinal-compact operator ideals
form a strictly increasing chain from `ℵ₀` through the successor of the actual
ambient Hilbert dimension. The bounded existence theorem for closed ideals
therefore has a unique threshold in this interval. No uniqueness is asserted
for larger cardinals, where the ideals have already reached `⊤`.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uH

namespace ContinuousLinearMap

/-- Real threshold comparison is reflected by inclusion of the actual ideals,
provided both thresholds lie in the valid interval. -/
theorem cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℝ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β)
    (hακ : α ≤ Order.succ (#ι)) (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα ≤
        cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) β hβ ↔ α ≤ β := by
  constructor
  · intro hle
    by_contra hn
    have hβα : β < α := lt_of_not_ge hn
    have hstrict := cardinalCompactOperatorIdeal_lt_of_lt_of_le_succ_mk_real
      (H := H) b hβ hα hβα hακ
    exact hstrict.2 hle
  · intro hαβ
    exact cardinalCompactOperatorIdeal_mono hα hβ hαβ

/-- Complex threshold comparison is reflected by inclusion of the actual
ideals, throughout the same valid interval. -/
theorem cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℂ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β)
    (hακ : α ≤ Order.succ (#ι)) (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα ≤
        cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) β hβ ↔ α ≤ β := by
  constructor
  · intro hle
    by_contra hn
    have hβα : β < α := lt_of_not_ge hn
    have hstrict := cardinalCompactOperatorIdeal_lt_of_lt_of_le_succ_mk_complex
      (H := H) b hβ hα hβα hακ
    exact hstrict.2 hle
  · intro hαβ
    exact cardinalCompactOperatorIdeal_mono hα hβ hαβ

/-- Equality of real cardinal-compact ideals reflects equality of thresholds
inside the valid interval. -/
theorem cardinalCompactOperatorIdeal_eq_iff_of_le_succ_mk_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℝ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β)
    (hακ : α ≤ Order.succ (#ι)) (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα =
        cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) β hβ ↔ α = β := by
  constructor
  · intro heq
    apply le_antisymm
    · exact (cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_real
        b hα hβ hακ hβκ).mp heq.le
    · exact (cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_real
        b hβ hα hβκ hακ).mp heq.ge
  · rintro rfl
    rfl

/-- Equality of complex cardinal-compact ideals reflects equality of
thresholds inside the valid interval. -/
theorem cardinalCompactOperatorIdeal_eq_iff_of_le_succ_mk_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type uH} (b : HilbertBasis ι ℂ H)
    {α β : Cardinal.{uH}} (hα : Cardinal.aleph0 ≤ α)
    (hβ : Cardinal.aleph0 ≤ β)
    (hακ : α ≤ Order.succ (#ι)) (hβκ : β ≤ Order.succ (#ι)) :
    cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα =
        cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) β hβ ↔ α = β := by
  constructor
  · intro heq
    apply le_antisymm
    · exact (cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_complex
        b hα hβ hακ hβκ).mp heq.le
    · exact (cardinalCompactOperatorIdeal_le_iff_of_le_succ_mk_complex
        b hβ hα hβκ hακ).mp heq.ge
  · rintro rfl
    rfl

end ContinuousLinearMap

namespace TwoSidedIdeal

/-- A nonzero norm-closed ideal on an infinite real Hilbert space has a unique
cardinal-compact threshold in the genuine interval determined by any actual
ambient Hilbert basis. -/
theorem existsUnique_cardinalCompact_threshold_of_isClosed_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (I : TwoSidedIdeal (H →L[ℝ] H))
    (hclosed : IsClosed (I : Set (H →L[ℝ] H))) (hI : I ≠ ⊥)
    (hInfinite : ¬ FiniteDimensional ℝ H) {ι : Type uH}
    (b : HilbertBasis ι ℝ H) :
    ∃! a : {α : Cardinal.{uH} //
      Cardinal.aleph0 ≤ α ∧ α ≤ Order.succ (#ι)},
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal
        (𝕜 := ℝ) (E := H) a.1 a.2.1 := by
  obtain ⟨α, hα, hακ, hIα⟩ :=
    I.exists_eq_cardinalCompactOperatorIdeal_with_lift_le_of_isClosed_real
      hclosed hI hInfinite b
  have hακ' : α ≤ Order.succ (#ι) := by
    simpa only [Cardinal.lift_id] using hακ
  refine ⟨⟨α, hα, hακ'⟩, hIα, ?_⟩
  rintro ⟨β, hβ, hβκ⟩ hIβ
  apply Subtype.ext
  exact ((ContinuousLinearMap.cardinalCompactOperatorIdeal_eq_iff_of_le_succ_mk_real
    b hα hβ hακ' hβκ).mp (hIα.symm.trans hIβ)).symm

/-- Complex counterpart of unique bounded threshold classification. -/
theorem existsUnique_cardinalCompact_threshold_of_isClosed_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (I : TwoSidedIdeal (H →L[ℂ] H))
    (hclosed : IsClosed (I : Set (H →L[ℂ] H))) (hI : I ≠ ⊥)
    (hInfinite : ¬ FiniteDimensional ℂ H) {ι : Type uH}
    (b : HilbertBasis ι ℂ H) :
    ∃! a : {α : Cardinal.{uH} //
      Cardinal.aleph0 ≤ α ∧ α ≤ Order.succ (#ι)},
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal
        (𝕜 := ℂ) (E := H) a.1 a.2.1 := by
  obtain ⟨α, hα, hακ, hIα⟩ :=
    I.exists_eq_cardinalCompactOperatorIdeal_with_lift_le_of_isClosed_complex
      hclosed hI hInfinite b
  have hακ' : α ≤ Order.succ (#ι) := by
    simpa only [Cardinal.lift_id] using hακ
  refine ⟨⟨α, hα, hακ'⟩, hIα, ?_⟩
  rintro ⟨β, hβ, hβκ⟩ hIβ
  apply Subtype.ext
  exact ((ContinuousLinearMap.cardinalCompactOperatorIdeal_eq_iff_of_le_succ_mk_complex
    b hα hβ hακ' hβκ).mp (hIα.symm.trans hIβ)).symm

/-- Complete real classification with the zero and finite-dimensional branches
kept separate from the unique infinite-dimensional threshold. -/
theorem eq_bot_or_finiteDimensional_eq_top_or_existsUnique_threshold_real
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (I : TwoSidedIdeal (H →L[ℝ] H))
    (hclosed : IsClosed (I : Set (H →L[ℝ] H))) {ι : Type uH}
    (b : HilbertBasis ι ℝ H) :
    I = ⊥ ∨
      (FiniteDimensional ℝ H ∧ I = ⊤) ∨
      (¬ FiniteDimensional ℝ H ∧
        ∃! a : {α : Cardinal.{uH} //
          Cardinal.aleph0 ≤ α ∧ α ≤ Order.succ (#ι)},
          I = ContinuousLinearMap.cardinalCompactOperatorIdeal
            (𝕜 := ℝ) (E := H) a.1 a.2.1) := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  by_cases hfin : FiniteDimensional ℝ H
  · letI := hfin
    exact Or.inl ⟨hfin, (I.eq_bot_or_eq_top_of_finiteDimensional).resolve_left hI⟩
  · exact Or.inr ⟨hfin,
      I.existsUnique_cardinalCompact_threshold_of_isClosed_real hclosed hI hfin b⟩

/-- Complete complex classification with the zero and finite-dimensional
branches kept separate from the unique infinite-dimensional threshold. -/
theorem eq_bot_or_finiteDimensional_eq_top_or_existsUnique_threshold_complex
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (I : TwoSidedIdeal (H →L[ℂ] H))
    (hclosed : IsClosed (I : Set (H →L[ℂ] H))) {ι : Type uH}
    (b : HilbertBasis ι ℂ H) :
    I = ⊥ ∨
      (FiniteDimensional ℂ H ∧ I = ⊤) ∨
      (¬ FiniteDimensional ℂ H ∧
        ∃! a : {α : Cardinal.{uH} //
          Cardinal.aleph0 ≤ α ∧ α ≤ Order.succ (#ι)},
          I = ContinuousLinearMap.cardinalCompactOperatorIdeal
            (𝕜 := ℂ) (E := H) a.1 a.2.1) := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  by_cases hfin : FiniteDimensional ℂ H
  · letI := hfin
    exact Or.inl ⟨hfin, (I.eq_bot_or_eq_top_of_finiteDimensional).resolve_left hI⟩
  · exact Or.inr ⟨hfin,
      I.existsUnique_cardinalCompact_threshold_of_isClosed_complex hclosed hI hfin b⟩

end TwoSidedIdeal
