/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.Normed.Operator.CardinalCompact
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Cardinal compactness and the Hilbert-space adjoint

The Gram-operator criterion is proved directly from internal nets on each
bounded set. Each old center has an actual preimage in that set; its image under
the original operator is a new internal center. The scalar bound and both Hilbert
space universes are independent. No regularity of the cardinal is used.

The equivalences hold for all cardinals (also the vacuous small-cardinal cases).
Only the statements about the existing two-sided ideal require `aleph0 ≤ α`.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Bornology
open scoped Cardinal

universe uF uH uK uA
variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace ContinuousLinearMap

/-- The squared norm is controlled by the norm of the Gram operator at the
same vector. This is an actual adjoint identity followed by Cauchy--Schwarz. -/
theorem norm_apply_sq_le_norm_adjoint_comp_self_mul (T : H →L[𝕜] K) (x : H) :
    ‖T x‖ ^ 2 ≤ ‖(T.adjoint.comp T) x‖ * ‖x‖ := by
  rw [T.apply_norm_sq_eq_inner_adjoint_left]
  exact re_inner_le_norm _ _

/-- An internal net for the Gram image of a bounded set gives an internal net
for its operator image. The center sets may lie in different universes. -/
theorem cardinalTotallyBounded_image_of_adjoint_comp_self
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} {B : Set H}
    (hB : Bornology.IsBounded B)
    (hQ : Metric.CardinalTotallyBounded α ((T.adjoint.comp T) '' B)) :
    Metric.CardinalTotallyBounded α (T '' B) := by
  classical
  intro ε hε
  obtain ⟨M, hM, hbound⟩ := hB.exists_pos_norm_le
  have hη : 0 < ε ^ 2 / (4 * M) := by positivity
  obtain ⟨c, hcB, hc, hcover⟩ := hQ (ε ^ 2 / (4 * M)) hη
  have hpre : ∀ j : c, ∃ x ∈ B, (T.adjoint.comp T) x = (j : H) :=
    fun j => hcB j.property
  choose z hzB hQz using hpre
  let d : Set K := Set.range (fun j : c => T (z j))
  let pick : c → d := fun j => ⟨T (z j), Set.mem_range_self j⟩
  have hpick : Function.Surjective pick := by
    rintro ⟨y, j, rfl⟩
    exact ⟨j, rfl⟩
  have hsize : Cardinal.lift.{uH} (#d) ≤ Cardinal.lift.{uK} (#c) :=
    Cardinal.lift_mk_le'.mpr ⟨Function.Embedding.ofSurjective pick hpick⟩
  have hs := Cardinal.lift_le.{uA}.mpr hsize
  have ht := Cardinal.lift_lt.{max uH uA, uK}.mpr hc
  simp only [Cardinal.lift_lift] at hs ht
  have hcommon : Cardinal.lift.{uH} (Cardinal.lift.{uA} (#d)) <
      Cardinal.lift.{uH} (Cardinal.lift.{uK} α) := by
    simpa only [Cardinal.lift_lift] using hs.trans_lt ht
  refine ⟨d, ?_, Cardinal.lift_lt.mp hcommon, ?_⟩
  · rintro y ⟨j, rfl⟩
    exact ⟨z j, hzB j, rfl⟩
  · rintro y ⟨x, hxB, rfl⟩
    obtain ⟨v, hvc, hxv⟩ := hcover ((T.adjoint.comp T) x) ⟨x, hxB, rfl⟩
    let j : c := ⟨v, hvc⟩
    have hQj : (T.adjoint.comp T) (z j) = v := hQz j
    have hq : ‖(T.adjoint.comp T) (x - z j)‖ < ε ^ 2 / (4 * M) := by
      simpa only [map_sub, hQj, dist_eq_norm] using hxv
    have hu : ‖x - z j‖ ≤ 2 * M :=
      (norm_sub_le x (z j)).trans (by linarith [hbound x hxB, hbound (z j) (hzB j)])
    have htwo : 0 < 2 * M := by positivity
    have hstrict : ‖(T.adjoint.comp T) (x - z j)‖ * (2 * M) < ε ^ 2 / 2 := by
      calc
        ‖(T.adjoint.comp T) (x - z j)‖ * (2 * M)
            < (ε ^ 2 / (4 * M)) * (2 * M) := mul_lt_mul_of_pos_right hq htwo
        _ = ε ^ 2 / 2 := by field_simp [ne_of_gt hM]; ring
    have hsq : ‖T (x - z j)‖ ^ 2 < ε ^ 2 := by
      have hle := (T.norm_apply_sq_le_norm_adjoint_comp_self_mul (x - z j)).trans
        (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
      have hεsq : 0 < ε ^ 2 := by positivity
      nlinarith
    have hdist : ‖T (x - z j)‖ < ε := by
      nlinarith [norm_nonneg (T (x - z j))]
    exact ⟨T (z j), Set.mem_range_self j, by
      simpa only [dist_eq_norm, map_sub] using hdist⟩

/-- A bounded Hilbert-space map is cardinal compact exactly when its Gram
operator is. There is no infinite-cardinal hypothesis on this equivalence. -/
theorem isCardinalCompactOperator_iff_adjoint_comp_self
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} :
    IsCardinalCompactOperator α T ↔ IsCardinalCompactOperator α (T.adjoint.comp T) := by
  constructor
  · exact fun hT => hT.clm_comp T.adjoint
  · intro hQ B hB
    exact T.cardinalTotallyBounded_image_of_adjoint_comp_self hB (hQ B hB)

end ContinuousLinearMap

namespace IsCardinalCompactOperator

/-- Cardinal compactness is preserved by the actual Hilbert adjoint. -/
theorem adjoint
    {T : H →L[𝕜] K} {α : Cardinal.{uA}} (hT : IsCardinalCompactOperator α T) :
    IsCardinalCompactOperator α T.adjoint := by
  apply (ContinuousLinearMap.isCardinalCompactOperator_iff_adjoint_comp_self T.adjoint).mpr
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hT.comp_clm T.adjoint

end IsCardinalCompactOperator

namespace ContinuousLinearMap

/-- Taking the adjoint preserves and reflects the existing bounded-image predicate. -/
theorem isCardinalCompactOperator_adjoint_iff
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} :
    IsCardinalCompactOperator α T.adjoint ↔ IsCardinalCompactOperator α T := by
  constructor
  · intro hT
    simpa only [adjoint_adjoint] using hT.adjoint
  · exact fun hT => hT.adjoint

/-- The co-Gram criterion follows by applying the Gram criterion to the adjoint. -/
theorem isCardinalCompactOperator_iff_self_comp_adjoint
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} :
    IsCardinalCompactOperator α T ↔ IsCardinalCompactOperator α (T.comp T.adjoint) := by
  have h := (isCardinalCompactOperator_adjoint_iff T (α := α)).symm.trans
    (isCardinalCompactOperator_iff_adjoint_comp_self T.adjoint)
  simpa only [adjoint_adjoint] using h

/-- Star preserves the carrier of the already constructed cardinal operator ideal. -/
theorem star_mem_cardinalCompactOperatorIdeal
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) {T : H →L[𝕜] H}
    (hT : T ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα) :
    star T ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα := by
  apply (mem_cardinalCompactOperatorIdeal α hα _).mpr
  change IsCardinalCompactOperator α T.adjoint
  exact ((mem_cardinalCompactOperatorIdeal α hα T).mp hT).adjoint

/-- The carrier is invariant, not merely mapped into itself, under star. -/
theorem star_mem_cardinalCompactOperatorIdeal_iff
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) (T : H →L[𝕜] H) :
    star T ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα ↔
      T ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα := by
  simp only [mem_cardinalCompactOperatorIdeal, star_eq_adjoint,
    isCardinalCompactOperator_adjoint_iff]

/-- Set-level star invariance of the same ideal, with its original operator norm. -/
theorem image_star_cardinalCompactOperatorIdeal
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    star '' (cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα : Set (H →L[𝕜] H)) =
      (cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα : Set (H →L[𝕜] H)) := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact star_mem_cardinalCompactOperatorIdeal α hα hS
  · intro hT
    exact ⟨star T, star_mem_cardinalCompactOperatorIdeal α hα hT, star_star T⟩

end ContinuousLinearMap
