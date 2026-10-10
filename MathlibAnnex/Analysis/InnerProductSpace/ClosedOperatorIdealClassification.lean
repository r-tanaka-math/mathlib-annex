/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.OperatorIdealHeightClassification

/-!
# Height classification of norm-closed operator ideals

The attained infinite-height case is algebraic: no norm-closedness or
star-closedness of the ideal is assumed. In the nonattained case the independent
small-closed-range ideal lies below I, and the bounded-image cardinal-compact
ideal lies above I. Only the final nonattained equality uses norm-closedness.

Real and complex statements apply the actual, field-specific range and closure
criteria already available. The zero ideal and finite-dimensional ambient space
are separate branches. Threshold uniqueness and strictness are not asserted.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uI

namespace TwoSidedIdeal

/-- In finite dimension a nonzero operator ideal is the whole operator ring,
which is the aleph-zero compact ideal. This is not an infinite-height formula. -/
theorem eq_cardinalCompactOperatorIdeal_aleph0_of_finiteDimensional
    {𝕜 : Type uF} [RCLike 𝕜] {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] [FiniteDimensional 𝕜 H]
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : I ≠ ⊥) :
    I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H)
      (Cardinal.aleph0 : Cardinal.{uH}) le_rfl := by
  have htop := (I.eq_bot_or_eq_top_of_finiteDimensional).resolve_left hI
  rw [htop, ContinuousLinearMap.cardinalCompactOperatorIdeal_aleph0_eq]
  exact ((ContinuousLinearMap.compactOperatorIdeal_eq_top_iff
    (𝕜 := 𝕜) (E := H)).mpr inferInstance).symm

section Real

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [hH : CompleteSpace H]

/-- Every literal-range dimension is at most the height, so every ideal member
is cardinal-compact at the successor of an infinite height. -/
theorem le_cardinalCompactOperatorIdeal_succ_hilbertHeight_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (h : Cardinal.aleph0 ≤ I.hilbertHeight) :
    I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
      (Order.succ I.hilbertHeight) (h.trans (Order.le_succ _)) := by
  intro T hT
  apply (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mpr
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_real
    (h.trans (Order.le_succ _))).mpr
  intro M hM hMT ι b
  have hb := I.hilbertBasis_lift_mk_le_hilbertHeight_of_le_range hT M hM hMT b
  have hb' : #ι ≤ I.hilbertHeight := by
    simpa only [Cardinal.lift_id] using hb
  simpa only [Cardinal.lift_id] using hb'.trans_lt (Order.lt_succ I.hilbertHeight)

/-- An attained infinite height determines the algebraic ideal itself.
Norm-closedness and star-closedness are not hypotheses. -/
theorem eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (h : Cardinal.aleph0 ≤ I.hilbertHeight)
    (hI : I.IsHilbertHeightAttained) :
    I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
      (Order.succ I.hilbertHeight) (h.trans (Order.le_succ _)) := by
  apply le_antisymm (I.le_cardinalCompactOperatorIdeal_succ_hilbertHeight_real h)
  intro T hT
  apply I.mem_of_hasSmallHilbertRange_succ_hilbertHeight hI
  exact (ContinuousLinearMap.hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_real
    I.hilbertHeight h T).mpr
      ((ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mp hT)

/-- Nonattainment gives a strict bound for every actual literal-range witness,
not a strict bound for the closed range of each ideal member. -/
theorem le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
      I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) := by
  intro T hT
  apply (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mpr
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_real
    (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI)).mpr
  intro M hM hMT ι b
  have hb := I.hilbertBasis_mk_mem_hilbertDimensions_of_le_range hT M hM hMT b
  simpa only [Cardinal.lift_id] using
    I.lt_hilbertHeight_of_not_isHilbertHeightAttained hI hb

/-- The two independently defined ideals bound any ideal of nonattained height.
Neither inclusion needs norm-closedness of I. -/
theorem cardinalRangeOperatorIdeal_le_and_le_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    let h := I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI
    ContinuousLinearMap.cardinalRangeOperatorIdeal (𝕜 := ℝ) (H := H)
        I.hilbertHeight h ≤ I ∧
      I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
        I.hilbertHeight h := by
  exact ⟨I.cardinalRangeOperatorIdeal_hilbertHeight_le _,
    I.le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_real hI⟩

/-- At a nonattained height the norm closure, rather than necessarily the
original algebraic ideal, is the cardinal-compact class. -/
theorem closure_eq_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    closure (I : Set (H →L[ℝ] H)) =
      (ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
        I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) :
        Set (H →L[ℝ] H)) := by
  let h := I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact I.le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_real hI
    · exact ContinuousLinearMap.isClosed_cardinalCompactOperatorIdeal _ h
  · intro T hT
    have hC : IsCardinalCompactOperator I.hilbertHeight T :=
      (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mp hT
    have hD : T ∈ closure {S : H →L[ℝ] H | HasSmallHilbertRange I.hilbertHeight S} := by
      rw [ContinuousLinearMap.closure_setOf_hasSmallHilbertRange_real
        I.hilbertHeight h]
      exact hC
    exact closure_mono (fun S hS => I.mem_of_hasSmallHilbertRange_hilbertHeight hS) hD

/-- Norm-closedness is used here, after the two algebraic inclusions, to identify
I with the cardinal-compact ideal at its nonattained height. -/
theorem eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hclosed : IsClosed (I : Set (H →L[ℝ] H)))
    (hI : ¬ I.IsHilbertHeightAttained) :
    I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H)
      I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) := by
  apply SetLike.coe_injective
  simpa only [hclosed.closure_eq] using
    I.closure_eq_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_real hI

include hH in
/-- Existence classification of all norm-closed two-sided operator ideals.
The zero ideal is a separate alternative, and finite-dimensional H uses the
aleph-zero threshold. No threshold uniqueness is asserted. -/
theorem eq_bot_or_exists_eq_cardinalCompactOperatorIdeal_of_isClosed_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hclosed : IsClosed (I : Set (H →L[ℝ] H))) :
    I = ⊥ ∨ ∃ (α : Cardinal.{uH}) (hα : Cardinal.aleph0 ≤ α),
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  by_cases hfin : FiniteDimensional ℝ H
  · letI := hfin
    exact ⟨Cardinal.aleph0, le_rfl,
      I.eq_cardinalCompactOperatorIdeal_aleph0_of_finiteDimensional hI⟩
  · have h := I.aleph0_le_hilbertHeight_of_ne_bot_of_not_finiteDimensional hI hfin
    by_cases hatt : I.IsHilbertHeightAttained
    · exact ⟨Order.succ I.hilbertHeight, h.trans (Order.le_succ _),
        I.eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_real h hatt⟩
    · exact ⟨I.hilbertHeight, h,
        I.eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_real
          hclosed hatt⟩

include hH in
/-- For a nonzero closed ideal on an infinite-dimensional space, the chosen
threshold is bounded by the successor of any actual ambient Hilbert-basis
cardinality, including a basis in a different index universe. -/
theorem exists_eq_cardinalCompactOperatorIdeal_with_lift_le_of_isClosed_real
    (I : TwoSidedIdeal (H →L[ℝ] H)) (hclosed : IsClosed (I : Set (H →L[ℝ] H)))
    (hI : I ≠ ⊥) (hInfinite : ¬ FiniteDimensional ℝ H)
    {ι : Type uI} (b : HilbertBasis ι ℝ H) :
    ∃ (α : Cardinal.{uH}) (hα : Cardinal.aleph0 ≤ α),
      Cardinal.lift.{uI} α ≤ Order.succ (Cardinal.lift.{uH} (#ι)) ∧
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) α hα := by
  classical
  have h := I.aleph0_le_hilbertHeight_of_ne_bot_of_not_finiteDimensional hI hInfinite
  have hbound := I.lift_hilbertHeight_le_mk b
  by_cases hatt : I.IsHilbertHeightAttained
  · refine ⟨Order.succ I.hilbertHeight, h.trans (Order.le_succ _), ?_,
      I.eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_real h hatt⟩
    rw [Cardinal.lift_succ]
    exact Order.succ_le_of_lt (hbound.trans_lt (Order.lt_succ _))
  · exact ⟨I.hilbertHeight, h, hbound.trans (Order.le_succ _),
      I.eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_real
        hclosed hatt⟩

end Real

section Complex

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [hH : CompleteSpace H]

/-- Every literal-range dimension is at most the height, so every ideal member
is cardinal-compact at the successor of an infinite height. -/
theorem le_cardinalCompactOperatorIdeal_succ_hilbertHeight_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (h : Cardinal.aleph0 ≤ I.hilbertHeight) :
    I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
      (Order.succ I.hilbertHeight) (h.trans (Order.le_succ _)) := by
  intro T hT
  apply (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mpr
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_complex
    (h.trans (Order.le_succ _))).mpr
  intro M hM hMT ι b
  have hb := I.hilbertBasis_lift_mk_le_hilbertHeight_of_le_range hT M hM hMT b
  have hb' : #ι ≤ I.hilbertHeight := by
    simpa only [Cardinal.lift_id] using hb
  simpa only [Cardinal.lift_id] using hb'.trans_lt (Order.lt_succ I.hilbertHeight)

/-- An attained infinite height determines the algebraic ideal itself.
Norm-closedness and star-closedness are not hypotheses. -/
theorem eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (h : Cardinal.aleph0 ≤ I.hilbertHeight)
    (hI : I.IsHilbertHeightAttained) :
    I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
      (Order.succ I.hilbertHeight) (h.trans (Order.le_succ _)) := by
  apply le_antisymm (I.le_cardinalCompactOperatorIdeal_succ_hilbertHeight_complex h)
  intro T hT
  apply I.mem_of_hasSmallHilbertRange_succ_hilbertHeight hI
  exact (ContinuousLinearMap.hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_complex
    I.hilbertHeight h T).mpr
      ((ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mp hT)

/-- Nonattainment gives a strict bound for every actual literal-range witness,
not a strict bound for the closed range of each ideal member. -/
theorem le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
      I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) := by
  intro T hT
  apply (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mpr
  apply (T.isCardinalCompactOperator_iff_forall_closed_submodule_complex
    (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI)).mpr
  intro M hM hMT ι b
  have hb := I.hilbertBasis_mk_mem_hilbertDimensions_of_le_range hT M hM hMT b
  simpa only [Cardinal.lift_id] using
    I.lt_hilbertHeight_of_not_isHilbertHeightAttained hI hb

/-- The two independently defined ideals bound any ideal of nonattained height.
Neither inclusion needs norm-closedness of I. -/
theorem cardinalRangeOperatorIdeal_le_and_le_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    let h := I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI
    ContinuousLinearMap.cardinalRangeOperatorIdeal (𝕜 := ℂ) (H := H)
        I.hilbertHeight h ≤ I ∧
      I ≤ ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
        I.hilbertHeight h := by
  exact ⟨I.cardinalRangeOperatorIdeal_hilbertHeight_le _,
    I.le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_complex hI⟩

/-- At a nonattained height the norm closure, rather than necessarily the
original algebraic ideal, is the cardinal-compact class. -/
theorem closure_eq_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    closure (I : Set (H →L[ℂ] H)) =
      (ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
        I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) :
        Set (H →L[ℂ] H)) := by
  let h := I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact I.le_cardinalCompactOperatorIdeal_hilbertHeight_of_not_isHilbertHeightAttained_complex hI
    · exact ContinuousLinearMap.isClosed_cardinalCompactOperatorIdeal _ h
  · intro T hT
    have hC : IsCardinalCompactOperator I.hilbertHeight T :=
      (ContinuousLinearMap.mem_cardinalCompactOperatorIdeal _ _ _).mp hT
    have hD : T ∈ closure {S : H →L[ℂ] H | HasSmallHilbertRange I.hilbertHeight S} := by
      rw [ContinuousLinearMap.closure_setOf_hasSmallHilbertRange_complex
        I.hilbertHeight h]
      exact hC
    exact closure_mono (fun S hS => I.mem_of_hasSmallHilbertRange_hilbertHeight hS) hD

/-- Norm-closedness is used here, after the two algebraic inclusions, to identify
I with the cardinal-compact ideal at its nonattained height. -/
theorem eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hclosed : IsClosed (I : Set (H →L[ℂ] H)))
    (hI : ¬ I.IsHilbertHeightAttained) :
    I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H)
      I.hilbertHeight (I.aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained hI) := by
  apply SetLike.coe_injective
  simpa only [hclosed.closure_eq] using
    I.closure_eq_cardinalCompactOperatorIdeal_of_not_isHilbertHeightAttained_complex hI

include hH in
/-- Existence classification of all norm-closed two-sided operator ideals.
The zero ideal is a separate alternative, and finite-dimensional H uses the
aleph-zero threshold. No threshold uniqueness is asserted. -/
theorem eq_bot_or_exists_eq_cardinalCompactOperatorIdeal_of_isClosed_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hclosed : IsClosed (I : Set (H →L[ℂ] H))) :
    I = ⊥ ∨ ∃ (α : Cardinal.{uH}) (hα : Cardinal.aleph0 ≤ α),
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  by_cases hfin : FiniteDimensional ℂ H
  · letI := hfin
    exact ⟨Cardinal.aleph0, le_rfl,
      I.eq_cardinalCompactOperatorIdeal_aleph0_of_finiteDimensional hI⟩
  · have h := I.aleph0_le_hilbertHeight_of_ne_bot_of_not_finiteDimensional hI hfin
    by_cases hatt : I.IsHilbertHeightAttained
    · exact ⟨Order.succ I.hilbertHeight, h.trans (Order.le_succ _),
        I.eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_complex h hatt⟩
    · exact ⟨I.hilbertHeight, h,
        I.eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_complex
          hclosed hatt⟩

include hH in
/-- For a nonzero closed ideal on an infinite-dimensional space, the chosen
threshold is bounded by the successor of any actual ambient Hilbert-basis
cardinality, including a basis in a different index universe. -/
theorem exists_eq_cardinalCompactOperatorIdeal_with_lift_le_of_isClosed_complex
    (I : TwoSidedIdeal (H →L[ℂ] H)) (hclosed : IsClosed (I : Set (H →L[ℂ] H)))
    (hI : I ≠ ⊥) (hInfinite : ¬ FiniteDimensional ℂ H)
    {ι : Type uI} (b : HilbertBasis ι ℂ H) :
    ∃ (α : Cardinal.{uH}) (hα : Cardinal.aleph0 ≤ α),
      Cardinal.lift.{uI} α ≤ Order.succ (Cardinal.lift.{uH} (#ι)) ∧
      I = ContinuousLinearMap.cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) α hα := by
  classical
  have h := I.aleph0_le_hilbertHeight_of_ne_bot_of_not_finiteDimensional hI hInfinite
  have hbound := I.lift_hilbertHeight_le_mk b
  by_cases hatt : I.IsHilbertHeightAttained
  · refine ⟨Order.succ I.hilbertHeight, h.trans (Order.le_succ _), ?_,
      I.eq_cardinalCompactOperatorIdeal_succ_hilbertHeight_of_isHilbertHeightAttained_complex h hatt⟩
    rw [Cardinal.lift_succ]
    exact Order.succ_le_of_lt (hbound.trans_lt (Order.lt_succ _))
  · exact ⟨I.hilbertHeight, h, hbound.trans (Order.le_succ _),
      I.eq_cardinalCompactOperatorIdeal_hilbertHeight_of_isClosed_of_not_isHilbertHeightAttained_complex
        hclosed hatt⟩

end Complex

end TwoSidedIdeal
