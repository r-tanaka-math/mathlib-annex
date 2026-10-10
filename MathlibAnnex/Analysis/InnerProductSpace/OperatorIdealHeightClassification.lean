/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.OperatorIdealHeight
import MathlibAnnex.Analysis.InnerProductSpace.CardinalRangeClosure
import Mathlib.Order.SuccPred.Limit

/-!
# Attained and nonattained heights of algebraic operator ideals

All dimensions refer to actual Hilbert bases. The existing height is reused;
its supremum is not assumed to be attained. Projection transfer gives membership
from a bound on a closed range. No ideal closedness or star-closedness is used
in this file. Finite-dimensional spans occur only in finite witness construction.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uI

namespace TwoSidedIdeal

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [hH : CompleteSpace H]

/-- A literal-range witness bounds any basis of that subspace by the actual
height. The basis index universe need not be the ambient universe. -/
theorem hilbertBasis_lift_mk_le_hilbertHeight_of_le_range
    (I : TwoSidedIdeal (H →L[𝕜] H)) {T : H →L[𝕜] H} (hT : T ∈ I)
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (hMT : M ≤ T.range)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 M) :
    Cardinal.lift.{uH} (#ι) ≤ Cardinal.lift.{uI} I.hilbertHeight := by
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 M
  have hw : #w ∈ I.hilbertDimensions := ⟨T, hT, M, hM, hMT, w, c, rfl⟩
  have hcb := c.lift_mk_le_of_denseRange b (ContinuousLinearMap.id 𝕜 M)
    (fun x => subset_closure ⟨x, rfl⟩)
  exact hcb.trans (Cardinal.lift_le.mpr (I.le_hilbertHeight_of_mem hw))

include hH in
/-- With an ambient-universe index, any chosen basis yields an actual member
of the dimension set, not merely a bound by its supremum. -/
theorem hilbertBasis_mk_mem_hilbertDimensions_of_le_range
    (I : TwoSidedIdeal (H →L[𝕜] H)) {T : H →L[𝕜] H} (hT : T ∈ I)
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (hMT : M ≤ T.range)
    {ι : Type uH} (b : HilbertBasis ι 𝕜 M) : #ι ∈ I.hilbertDimensions := by
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 M
  have he : #w = #ι := by
    simpa only [Cardinal.lift_id] using
      c.lift_mk_eq_of_continuous_linear_equiv b (ContinuousLinearEquiv.refl 𝕜 M)
  exact ⟨T, hT, M, hM, hMT, w, c, he⟩

/-- The actual height is bounded by any ambient Hilbert basis, with lifts. -/
theorem lift_hilbertHeight_le_mk (I : TwoSidedIdeal (H →L[𝕜] H))
    {ι : Type uI} (b : HilbertBasis ι 𝕜 H) :
    Cardinal.lift.{uI} I.hilbertHeight ≤ Cardinal.lift.{uH} (#ι) := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 H
  have hc : Cardinal.lift.{uI} I.hilbertHeight ≤ Cardinal.lift.{uI} (#w) :=
    Cardinal.lift_le.mpr (I.hilbertHeight_le_mk c)
  have hcb := b.lift_mk_le_of_denseRange c (ContinuousLinearMap.id 𝕜 H)
    (fun x => subset_closure ⟨x, rfl⟩)
  exact hc.trans hcb

/-- Every bound strictly below the supremum is exceeded by an actual witness.
This statement makes no attainment assumption. -/
theorem exists_mem_hilbertDimensions_gt_of_lt_hilbertHeight
    (I : TwoSidedIdeal (H →L[𝕜] H)) {γ : Cardinal.{uH}}
    (hγ : γ < I.hilbertHeight) : ∃ d ∈ I.hilbertDimensions, γ < d := by
  by_contra! h
  exact hγ.not_ge (I.hilbertHeight_le h)

/-- Nonattainment turns the supremum bound of each witness into a strict bound. -/
theorem lt_hilbertHeight_of_not_isHilbertHeightAttained
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : ¬ I.IsHilbertHeightAttained)
    {d : Cardinal.{uH}} (hd : d ∈ I.hilbertDimensions) : d < I.hilbertHeight := by
  refine lt_of_le_of_ne (I.le_hilbertHeight_of_mem hd) ?_
  intro he
  apply hI
  change I.hilbertHeight ∈ I.hilbertDimensions
  simpa only [he] using hd

/-- An unachieved supremum of the nonempty dimension set is a nonzero
successor-limit cardinal. Inaccessibility here is nonattainment, not a
large-cardinal regularity assumption. -/
theorem isSuccLimit_hilbertHeight_of_not_isHilbertHeightAttained
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    Order.IsSuccLimit I.hilbertHeight := by
  apply Order.isSuccLimit_iff_of_orderBot.mpr
  constructor
  · intro hz
    apply hI
    change I.hilbertHeight ∈ I.hilbertDimensions
    rw [hz]
    exact I.zero_mem_hilbertDimensions
  · apply Order.isSuccPrelimit_of_succ_lt
    intro γ hγ
    obtain ⟨d, hd, hγd⟩ := I.exists_mem_hilbertDimensions_gt_of_lt_hilbertHeight hγ
    exact (Order.succ_le_of_lt hγd).trans_lt
      (I.lt_hilbertHeight_of_not_isHilbertHeightAttained hI hd)

/-- In particular a nonattained height is at least the first infinite cardinal. -/
theorem aleph0_le_hilbertHeight_of_not_isHilbertHeightAttained
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : ¬ I.IsHilbertHeightAttained) :
    Cardinal.aleph0 ≤ I.hilbertHeight :=
  Cardinal.aleph0_le_of_isSuccLimit
    (I.isSuccLimit_hilbertHeight_of_not_isHilbertHeightAttained hI)

include hH in
/-- A projection with dimension at most an actual dimension witness belongs
to the ideal. The two Hilbert-basis index universes may differ. -/
theorem starProjection_mem_of_lift_mk_le_of_mem_hilbertDimensions
    (I : TwoSidedIdeal (H →L[𝕜] H)) {d : Cardinal.{uH}}
    (hd : d ∈ I.hilbertDimensions) (N : Submodule 𝕜 H)
    (hN : IsClosed (N : Set H)) {ι : Type uI} (b : HilbertBasis ι 𝕜 N)
    (hb : Cardinal.lift.{uH} (#ι) ≤ Cardinal.lift.{uI} d) :
    letI : CompleteSpace N := hN.completeSpace_coe
    N.starProjection ∈ I := by
  obtain ⟨T, hT, M, hM, hMT, w, c, hc⟩ := hd
  exact I.starProjection_mem_of_lift_mk_le_of_le_range hT M N hM hN hMT b c
    (by simpa only [hc] using hb)

include hH in
/-- Once the projection onto the closed range is in the ideal, multiplication
by the original operator gives membership. No closedness of the ideal is used. -/
theorem mem_of_closure_range_lift_mk_le_of_mem_hilbertDimensions
    (I : TwoSidedIdeal (H →L[𝕜] H)) (T : H →L[𝕜] H)
    {d : Cardinal.{uH}} (hd : d ∈ I.hilbertDimensions)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 T.range.topologicalClosure)
    (hb : Cardinal.lift.{uH} (#ι) ≤ Cardinal.lift.{uI} d) : T ∈ I := by
  let N := T.range.topologicalClosure
  have hN : IsClosed (N : Set H) := T.range.isClosed_topologicalClosure
  letI : CompleteSpace N := hN.completeSpace_coe
  have hP := I.starProjection_mem_of_lift_mk_le_of_mem_hilbertDimensions hd N hN b hb
  have he : N.starProjection * T = T := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr
      (T.range.le_topologicalClosure (T.mem_range_self x))
  rw [← he]
  exact I.mul_mem_right _ _ hP

/-- An attained height absorbs every operator with closed-range dimension at
most that height. The successor bound is a cardinal successor, not addition. -/
theorem mem_of_hasSmallHilbertRange_succ_hilbertHeight
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : I.IsHilbertHeightAttained)
    {T : H →L[𝕜] H} (hT : HasSmallHilbertRange (Order.succ I.hilbertHeight) T) :
    T ∈ I := by
  obtain ⟨ι, b, hb⟩ := hT
  apply I.mem_of_closure_range_lift_mk_le_of_mem_hilbertDimensions T hI b
  simpa only [Cardinal.lift_id, Order.lt_succ_iff] using hb

/-- All strictly smaller closed ranges are absorbed by any ideal of this
height. An actual larger witness is chosen before projection transfer. -/
theorem mem_of_hasSmallHilbertRange_hilbertHeight
    (I : TwoSidedIdeal (H →L[𝕜] H)) {T : H →L[𝕜] H}
    (hT : HasSmallHilbertRange I.hilbertHeight T) : T ∈ I := by
  obtain ⟨ι, b, hb⟩ := hT
  have hb' : #ι < I.hilbertHeight := by simpa only [Cardinal.lift_id] using hb
  obtain ⟨d, hd, hbd⟩ := I.exists_mem_hilbertDimensions_gt_of_lt_hilbertHeight hb'
  exact I.mem_of_closure_range_lift_mk_le_of_mem_hilbertDimensions T hd b
    (by simpa only [Cardinal.lift_id] using hbd.le)

/-- The independent small-closed-range ideal is contained in an ideal of
height h. The infinite-bound hypothesis is exactly that of its existing type. -/
theorem cardinalRangeOperatorIdeal_hilbertHeight_le
    (I : TwoSidedIdeal (H →L[𝕜] H)) (h : Cardinal.aleph0 ≤ I.hilbertHeight) :
    ContinuousLinearMap.cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H)
      I.hilbertHeight h ≤ I := by
  intro T hT
  exact I.mem_of_hasSmallHilbertRange_hilbertHeight
    ((ContinuousLinearMap.mem_cardinalRangeOperatorIdeal _ _ _).mp hT)

include hH in
/-- Every finite dimension is realized in a nonzero operator ideal on an
infinite-dimensional Hilbert space. Only the finite span used at this step is
identified with a finite algebraic basis. -/
theorem natCast_mem_hilbertDimensions_of_ne_bot_of_not_finiteDimensional
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : I ≠ ⊥)
    (hInfinite : ¬ FiniteDimensional 𝕜 H) (n : ℕ) :
    (n : Cardinal.{uH}) ∈ I.hilbertDimensions := by
  classical
  obtain ⟨wH, bH, -⟩ := exists_hilbertBasis 𝕜 H
  rcases finite_or_infinite wH with hf | hi
  · letI : Finite wH := hf
    letI : Fintype wH := Fintype.ofFinite wH
    exact (hInfinite (Module.Finite.of_basis bH.toOrthonormalBasis.toBasis)).elim
  · letI : Infinite wH := hi
    have hcard : Cardinal.lift.{uH} (#(Fin n)) ≤ Cardinal.lift.{0} (#wH) := by
      simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
        (Cardinal.natCast_lt_aleph0 : (n : Cardinal.{uH}) < Cardinal.aleph0).le.trans
          (Cardinal.aleph0_le_mk wH)
    obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hcard
    let v : Fin n → H := fun i => bH (f i)
    have hv : Orthonormal 𝕜 v := bH.orthonormal.comp f f.injective
    let M : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range v)
    letI : FiniteDimensional 𝕜 M := Module.Finite.span_of_finite 𝕜 (Set.finite_range v)
    have hM : IsClosed (M : Set H) := Submodule.closed_of_finiteDimensional M
    letI : CompleteSpace M := hM.completeSpace_coe
    have hdim : Module.finrank 𝕜 M = n := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hv.linearIndependent
    obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 M
    letI : Finite w := b.orthonormal.linearIndependent.finite
    letI : Fintype w := Fintype.ofFinite w
    have hb : #w = (n : Cardinal.{uH}) := by
      rw [Cardinal.mk_fintype, ← Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis, hdim]
    haveI : FiniteDimensional 𝕜 M.starProjection.range := by
      rw [Submodule.range_starProjection]
      infer_instance
    have hP := I.mem_of_finiteDimensional_range hI M.starProjection
    exact (I.mem_hilbertDimensions_iff_exists_starProjection_mem n).mpr
      ⟨M, hM, hP, w, b, hb⟩

/-- A nonzero operator ideal on an infinite-dimensional Hilbert space has
height at least aleph-zero. No norm closedness is needed. -/
theorem aleph0_le_hilbertHeight_of_ne_bot_of_not_finiteDimensional
    (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : I ≠ ⊥)
    (hInfinite : ¬ FiniteDimensional 𝕜 H) : Cardinal.aleph0 ≤ I.hilbertHeight := by
  by_contra hn
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (lt_of_not_ge hn)
  have hs := I.le_hilbertHeight_of_mem
    (I.natCast_mem_hilbertDimensions_of_ne_bot_of_not_finiteDimensional hI hInfinite (n + 1))
  rw [hn] at hs
  have hf : n + 1 ≤ n := by exact_mod_cast hs
  omega

end TwoSidedIdeal
