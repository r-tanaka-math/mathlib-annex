/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CardinalRangeIdeal
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactRellich
import Mathlib.Topology.Sequences
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

/-!
# Norm closure of the small-closed-range ideal

At each error tolerance the actual operator `T ∘ P_M` has small closed range.
The norm error is bounded by the norm of the restriction to `Mᗮ`. Rellich's
criterion therefore proves that the norm closure of the independently defined
small-closed-range class is precisely the bounded-image cardinal-compact class.

For a successor bound `Order.succ β`, `aleph0 ≤ β`, the same β bounds every
approximating closed range. A single countable family of basis generators then
has cardinal at most β. This argument is not used at arbitrary limit cardinals.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open scoped Cardinal Topology

universe uF uH uK uI uA
namespace ContinuousLinearMap

section Projection

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

include hK in
/-- Composing with the orthogonal projection onto a small closed subspace
produces a small closed range, even if the image of that subspace is not closed. -/
theorem hasSmallHilbertRange_comp_starProjection (T : H →L[𝕜] K)
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) [CompleteSpace H]
    {α : Cardinal.{uA}} {ι : Type uI} (b : HilbertBasis ι 𝕜 M)
    (hb : Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α) :
    letI : CompleteSpace M := hM.completeSpace_coe
    HasSmallHilbertRange α (T.comp M.starProjection) := by
  letI : CompleteSpace M := hM.completeSpace_coe
  let q : M →L[𝕜] K := T.comp M.subtypeL
  letI : CompleteSpace q.range.topologicalClosure :=
    q.range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 q.range.topologicalClosure
  have hq : HasSmallHilbertRange α q :=
    ⟨κ, c, b.lift_mk_lt_of_denseRange c q.toClosureRange q.denseRange_toClosureRange hb⟩
  have heq : q.comp M.orthogonalProjectionOnto = T.comp M.starProjection := by
    ext x
    rfl
  rw [← heq]
  exact hq.comp_right M.orthogonalProjectionOnto

end Projection

section NormEstimate

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

include hH in
/-- The error is controlled in the original operator norm, not only on finite
sets of test vectors. No projection into a separate research algebra is assumed. -/
theorem norm_sub_comp_starProjection_le (T : H →L[𝕜] K)
    (M : Submodule 𝕜 H) [CompleteSpace M] :
    ‖T - T.comp M.starProjection‖ ≤ ‖T.comp Mᗮ.subtypeL‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hr : x - M.starProjection x ∈ Mᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hn : ‖x - M.starProjection x‖ ≤ ‖x‖ := by
    simpa only [Submodule.starProjection_orthogonal_val] using
      Mᗮ.norm_starProjection_apply_le x
  calc
    ‖(T - T.comp M.starProjection) x‖ =
        ‖(T.comp Mᗮ.subtypeL) ⟨x - M.starProjection x, hr⟩‖ := by
      change ‖T x - T (M.starProjection x)‖ = ‖T (x - M.starProjection x)‖
      rw [map_sub]
    _ ≤ ‖T.comp Mᗮ.subtypeL‖ * ‖x - M.starProjection x‖ :=
      (T.comp Mᗮ.subtypeL).le_opNorm _
    _ ≤ ‖T.comp Mᗮ.subtypeL‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)

end NormEstimate

section Closure

variable {H : Type uH} [NormedAddCommGroup H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [hK : CompleteSpace K]

include hH hK in
/-- Real cardinal-compact operators admit arbitrarily close actual operators
whose closed ranges have strictly small Hilbert bases. -/
theorem exists_hasSmallHilbertRange_norm_sub_lt_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (T : H →L[ℝ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hT : IsCardinalCompactOperator α T) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : H →L[ℝ] K, HasSmallHilbertRange α A ∧ ‖T - A‖ < ε := by
  obtain ⟨M, hM, ι, b, hb, hn⟩ :=
    (T.isCardinalCompactOperator_iff_rellich_real hα).mp hT ε hε
  letI : CompleteSpace M := hM.completeSpace_coe
  exact ⟨T.comp M.starProjection, T.hasSmallHilbertRange_comp_starProjection M hM b hb,
    (T.norm_sub_comp_starProjection_le M).trans_lt hn⟩

include hH hK in
/-- The complex specialization uses the existing complex Rellich theorem.
It does not reconstruct a cutoff or assume the full range is closed. -/
theorem exists_hasSmallHilbertRange_norm_sub_lt_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hT : IsCardinalCompactOperator α T) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : H →L[ℂ] K, HasSmallHilbertRange α A ∧ ‖T - A‖ < ε := by
  obtain ⟨M, hM, ι, b, hb, hn⟩ :=
    (T.isCardinalCompactOperator_iff_rellich_complex hα).mp hT ε hε
  letI : CompleteSpace M := hM.completeSpace_coe
  exact ⟨T.comp M.starProjection, T.hasSmallHilbertRange_comp_starProjection M hM b hb,
    (T.norm_sub_comp_starProjection_le M).trans_lt hn⟩

include hH hK in
/-- The norm closure of the real small-closed-range class is the independently
constructed bounded-image cardinal-compact class. -/
theorem closure_setOf_hasSmallHilbertRange_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    closure {T : H →L[ℝ] K | HasSmallHilbertRange α T} =
      {T : H →L[ℝ] K | IsCardinalCompactOperator α T} := by
  apply le_antisymm
  · exact closure_minimal (fun _ h => h.isCardinalCompactOperator hα)
      (isClosed_setOf_isCardinalCompactOperator (α := α))
  · intro T hT
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨A, hA, hn⟩ := T.exists_hasSmallHilbertRange_norm_sub_lt_real hα hT hε
    exact ⟨A, hA, by simpa only [dist_eq_norm] using hn⟩

include hH hK in
/-- The corresponding closure equality for complex Hilbert spaces. -/
theorem closure_setOf_hasSmallHilbertRange_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    closure {T : H →L[ℂ] K | HasSmallHilbertRange α T} =
      {T : H →L[ℂ] K | IsCardinalCompactOperator α T} := by
  apply le_antisymm
  · exact closure_minimal (fun _ h => h.isCardinalCompactOperator hα)
      (isClosed_setOf_isCardinalCompactOperator (α := α))
  · intro T hT
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨A, hA, hn⟩ := T.exists_hasSmallHilbertRange_norm_sub_lt_complex hα hT hε
    exact ⟨A, hA, by simpa only [dist_eq_norm] using hn⟩

end Closure
end ContinuousLinearMap

namespace ContinuousLinearMap

section Successor

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

include hK in
/-- A sequential limit of small-closed-range operators retains the bound at
an infinite successor. Every approximating range has the same upper bound β;
no assertion about arbitrary countable unions of `< α` cardinals is made. -/
theorem hasSmallHilbertRange_succ_of_tendsto (β : Cardinal.{uA})
    (hβ : Cardinal.aleph0 ≤ β) {A : ℕ → H →L[𝕜] K} {T : H →L[𝕜] K}
    (hA : ∀ n, HasSmallHilbertRange (Order.succ β) (A n))
    (hlim : Tendsto A atTop (𝓝 T)) : HasSmallHilbertRange (Order.succ β) T := by
  classical
  choose ι b hb using hA
  have hbound : ∀ n, Cardinal.lift.{uA} (#(ι n)) ≤ Cardinal.lift.{uK} β := by
    intro n
    simpa only [Cardinal.lift_succ, Order.lt_succ_iff] using hb n
  have hemb : ∀ n, Nonempty (ι n ↪ β.out) := by
    intro n
    apply Cardinal.lift_mk_le'.mp
    simpa only [Cardinal.mk_out] using hbound n
  let emb : ∀ n, ι n ↪ β.out := fun n => Classical.choice (hemb n)
  let g : (Σ n : ℕ, ι n) ↪ ℕ × β.out :=
    ⟨fun z => (z.1, emb z.1 z.2), by
      rintro ⟨n, i⟩ ⟨m, j⟩ h
      have hn : n = m := congrArg Prod.fst h
      subst m
      have hi : i = j := (emb n).injective (congrArg Prod.snd h)
      subst j
      rfl⟩
  have hsig : Cardinal.lift.{uA} (#(Σ n : ℕ, ι n)) ≤ Cardinal.lift.{uK} β := by
    have h := Cardinal.lift_mk_le'.mpr (⟨g⟩ : Nonempty ((Σ n : ℕ, ι n) ↪ ℕ × β.out))
    simpa only [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_aleph0,
      Cardinal.lift_uzero, Cardinal.mk_out, Cardinal.aleph0_mul_eq hβ] using h
  let v : (Σ n : ℕ, ι n) → K := fun z => (b z.1 z.2 : K)
  let L : Submodule 𝕜 K := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
  have hL : IsClosed (L : Set K) :=
    (Submodule.span 𝕜 (Set.range v)).isClosed_topologicalClosure
  letI : CompleteSpace L := hL.completeSpace_coe
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 L
  have hdim : Cardinal.lift.{uA} (#κ) ≤ Cardinal.lift.{uK} β := by
    have hle : #κ ≤ #(Σ n : ℕ, ι n) := by
      simpa only [Cardinal.lift_id] using HilbertBasis.lift_mk_le_closed_span v c
    exact (Cardinal.lift_le.mpr hle).trans hsig
  have hAL : ∀ n, (A n).range.topologicalClosure ≤ L := by
    intro n
    apply (b n).submodule_le_of_forall_mem hL
    intro i
    exact (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
      (Submodule.subset_span ⟨⟨n, i⟩, rfl⟩)
  have hTL : T.range ≤ L := by
    rintro y ⟨x, rfl⟩
    apply hL.mem_of_tendsto ((ContinuousLinearMap.apply 𝕜 K x).continuous.tendsto T |>.comp hlim)
    exact Filter.Eventually.of_forall fun n =>
      hAL n ((A n).range.le_topologicalClosure ((A n).mem_range_self x))
  apply T.hasSmallHilbertRange_of_range_le L hL hTL c
  exact hdim.trans_lt (Cardinal.lift_lt.mpr (Order.lt_succ β))

include hK in
/-- At a successor of an infinite cardinal the small-closed-range class is
norm closed. This is not asserted for `aleph0` or for general limit bounds. -/
theorem isClosed_setOf_hasSmallHilbertRange_succ (β : Cardinal.{uA})
    (hβ : Cardinal.aleph0 ≤ β) :
    IsClosed {T : H →L[𝕜] K | HasSmallHilbertRange (Order.succ β) T} := by
  apply (isSeqClosed_iff_isClosed).mp
  intro A T hA hlim
  exact hasSmallHilbertRange_succ_of_tendsto β hβ hA hlim

end Successor

section SuccessorEquality

variable {H : Type uH} [NormedAddCommGroup H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [hK : CompleteSpace K]

include hH hK in
/-- Successor equality in the real case, obtained from the independent norm
closure theorem and the common-bound sequential argument. -/
theorem hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (β : Cardinal.{uA}) (hβ : Cardinal.aleph0 ≤ β) (T : H →L[ℝ] K) :
    HasSmallHilbertRange (Order.succ β) T ↔
      IsCardinalCompactOperator (Order.succ β) T := by
  have hα : Cardinal.aleph0 ≤ Order.succ β := hβ.trans (Order.le_succ β)
  have heq := closure_setOf_hasSmallHilbertRange_real (H := H) (K := K) (Order.succ β) hα
  rw [(isClosed_setOf_hasSmallHilbertRange_succ (𝕜 := ℝ) (H := H) (K := K) β hβ).closure_eq]
    at heq
  exact Set.ext_iff.mp heq T

include hH hK in
/-- The complex successor equality. The successor operation is `Order.succ`
on cardinals, not addition of the finite cardinal one. -/
theorem hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (β : Cardinal.{uA}) (hβ : Cardinal.aleph0 ≤ β) (T : H →L[ℂ] K) :
    HasSmallHilbertRange (Order.succ β) T ↔
      IsCardinalCompactOperator (Order.succ β) T := by
  have hα : Cardinal.aleph0 ≤ Order.succ β := hβ.trans (Order.le_succ β)
  have heq := closure_setOf_hasSmallHilbertRange_complex (H := H) (K := K) (Order.succ β) hα
  rw [(isClosed_setOf_hasSmallHilbertRange_succ (𝕜 := ℂ) (H := H) (K := K) β hβ).closure_eq]
    at heq
  exact Set.ext_iff.mp heq T

include hH in
/-- The two literal operator ideals coincide at a real infinite successor. -/
theorem cardinalRangeOperatorIdeal_succ_eq_cardinalCompactOperatorIdeal_real
    [InnerProductSpace ℝ H] (β : Cardinal.{uA}) (hβ : Cardinal.aleph0 ≤ β) :
    cardinalRangeOperatorIdeal (𝕜 := ℝ) (H := H) (Order.succ β)
        (hβ.trans (Order.le_succ β)) =
      cardinalCompactOperatorIdeal (𝕜 := ℝ) (E := H) (Order.succ β)
        (hβ.trans (Order.le_succ β)) := by
  ext T
  simp only [mem_cardinalRangeOperatorIdeal, mem_cardinalCompactOperatorIdeal]
  exact hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_real β hβ T

include hH in
/-- The corresponding equality of complex operator ideals. -/
theorem cardinalRangeOperatorIdeal_succ_eq_cardinalCompactOperatorIdeal_complex
    [InnerProductSpace ℂ H] (β : Cardinal.{uA}) (hβ : Cardinal.aleph0 ≤ β) :
    cardinalRangeOperatorIdeal (𝕜 := ℂ) (H := H) (Order.succ β)
        (hβ.trans (Order.le_succ β)) =
      cardinalCompactOperatorIdeal (𝕜 := ℂ) (E := H) (Order.succ β)
        (hβ.trans (Order.le_succ β)) := by
  ext T
  simp only [mem_cardinalRangeOperatorIdeal, mem_cardinalCompactOperatorIdeal]
  exact hasSmallHilbertRange_succ_iff_isCardinalCompactOperator_complex β hβ T

end SuccessorEquality
end ContinuousLinearMap
