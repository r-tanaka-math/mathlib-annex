/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.OperatorIdealProjection
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisRangeCardinality
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Bounded Hilbert dimensions and height of an operator ideal

Dimensions are cardinalities of genuine Hilbert-basis index sets. The witnesses
are closed subspaces contained in literal ranges of ideal members. Boundedness
and smallness are proved before taking the cardinal supremum. Attainment is a
separate predicate, never an automatic consequence of boundedness.

This file does not classify ideals. It assumes neither norm-closedness nor
star-closedness of the ideal. The zero ideal is handled explicitly.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uI

namespace TwoSidedIdeal

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The set of Hilbert dimensions of closed subspaces of literal operator ranges
from the ideal. Index sets are subsets of the subspaces, hence live in the
ambient universe. The arbitrary-universe comparison is supplied separately. -/
def hilbertDimensions (I : TwoSidedIdeal (H →L[𝕜] H)) : Set Cardinal.{uH} :=
  {d | ∃ T : H →L[𝕜] H, T ∈ I ∧ ∃ M : Submodule 𝕜 H,
    IsClosed (M : Set H) ∧ M ≤ T.range ∧
    ∃ w : Set M, ∃ b : HilbertBasis w 𝕜 M, #w = d}

variable [hH : CompleteSpace H]

include hH in
/-- Each witnessed dimension is at most that of any given ambient Hilbert basis,
with explicit lifts for different universes. -/
theorem lift_le_of_mem_hilbertDimensions (I : TwoSidedIdeal (H →L[𝕜] H))
    {ι : Type uI} (bH : HilbertBasis ι 𝕜 H) {d : Cardinal.{uH}}
    (hd : d ∈ I.hilbertDimensions) :
    Cardinal.lift.{uI} d ≤ Cardinal.lift.{uH} (#ι) := by
  obtain ⟨T, hT, M, hM, hMT, w, b, hd⟩ := hd
  letI : CompleteSpace M := hM.completeSpace_coe
  have hq : Surjective M.orthogonalProjectionOnto := by
    intro x
    exact ⟨x, M.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  have h := bH.lift_mk_le_of_denseRange b M.orthogonalProjectionOnto hq.denseRange
  simpa only [hd] using h

include hH in
/-- The dimension set is genuinely bounded in its own cardinal universe. -/
theorem bddAbove_hilbertDimensions (I : TwoSidedIdeal (H →L[𝕜] H)) :
    BddAbove I.hilbertDimensions := by
  obtain ⟨w, bH, hbH⟩ := exists_hilbertBasis 𝕜 H
  refine ⟨#w, fun d hd => ?_⟩
  simpa only [Cardinal.lift_id] using I.lift_le_of_mem_hilbertDimensions bH hd

include hH in
/-- In particular the dimension set is small in the ambient Hilbert universe. -/
theorem small_hilbertDimensions (I : TwoSidedIdeal (H →L[𝕜] H)) :
    Small.{uH} I.hilbertDimensions :=
  Cardinal.bddAbove_iff_small.mp I.bddAbove_hilbertDimensions

include hH in
/-- Zero is always witnessed by the zero operator and the zero subspace. -/
theorem zero_mem_hilbertDimensions (I : TwoSidedIdeal (H →L[𝕜] H)) :
    0 ∈ I.hilbertDimensions := by
  let M : Submodule 𝕜 H := ⊥
  have hM : IsClosed (M : Set H) := by
    change IsClosed ({0} : Set H)
    exact isClosed_singleton
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 M
  have hz : ∀ x : M, x = 0 := by
    intro x
    apply Subtype.ext
    exact x.property
  have hw : IsEmpty w := ⟨fun i => by
    have hn := b.orthonormal.1 i
    rw [hz (b i), norm_zero] at hn
    exact zero_ne_one hn⟩
  exact ⟨0, I.zero_mem, M, hM, bot_le, w, b, Cardinal.mk_eq_zero_iff.mpr hw⟩

include hH in
/-- The dimension set is nonempty, even when the ideal or space is zero. -/
theorem hilbertDimensions_nonempty (I : TwoSidedIdeal (H →L[𝕜] H)) :
    I.hilbertDimensions.Nonempty := ⟨0, I.zero_mem_hilbertDimensions⟩

include hH in
/-- Projection extraction identifies the same dimension set using actual ideal
projections. This is an equivalence, not a replacement definition. -/
theorem mem_hilbertDimensions_iff_exists_starProjection_mem
    (I : TwoSidedIdeal (H →L[𝕜] H)) (d : Cardinal.{uH}) :
    d ∈ I.hilbertDimensions ↔
      ∃ (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)),
        (letI : CompleteSpace M := hM.completeSpace_coe
         M.starProjection ∈ I) ∧
        ∃ w : Set M, ∃ b : HilbertBasis w 𝕜 M, #w = d := by
  constructor
  · rintro ⟨T, hT, M, hM, hMT, w, b, hd⟩
    exact ⟨M, hM, I.starProjection_mem_of_le_range hT M hM hMT, w, b, hd⟩
  · rintro ⟨M, hM, hP, w, b, hd⟩
    letI : CompleteSpace M := hM.completeSpace_coe
    refine ⟨M.starProjection, hP, M, hM, ?_, w, b, hd⟩
    rw [Submodule.range_starProjection]

/-- Ideal inclusion preserves all witnessed dimensions. -/
theorem hilbertDimensions_mono {I J : TwoSidedIdeal (H →L[𝕜] H)} (h : I ≤ J) :
    I.hilbertDimensions ⊆ J.hilbertDimensions := by
  rintro d ⟨T, hT, M, hM, hMT, w, b, hd⟩
  exact ⟨T, h hT, M, hM, hMT, w, b, hd⟩

include hH in
/-- The zero ideal has precisely the zero dimension, not an empty witness set. -/
theorem hilbertDimensions_bot :
    (⊥ : TwoSidedIdeal (H →L[𝕜] H)).hilbertDimensions = {0} := by
  ext d
  constructor
  · rintro ⟨T, hT, M, hM, hMT, w, b, hd⟩
    have hT0 : T = 0 := (TwoSidedIdeal.mem_bot (x := T)).mp hT
    have hz : ∀ x : M, x = 0 := by
      intro x
      apply Subtype.ext
      obtain ⟨y, hy⟩ := hMT x.property
      change T y = (x : H) at hy
      change (x : H) = 0
      simpa only [hT0, zero_apply] using hy.symm
    have hw : IsEmpty w := ⟨fun i => by
      have hn := b.orthonormal.1 i
      rw [hz (b i), norm_zero] at hn
      exact zero_ne_one hn⟩
    exact Set.mem_singleton_iff.mpr (hd.symm.trans (Cardinal.mk_eq_zero_iff.mpr hw))
  · rintro rfl
    exact (⊥ : TwoSidedIdeal (H →L[𝕜] H)).zero_mem_hilbertDimensions

include hH in
/-- The height is taken only after the dimension set's boundedness has been
established. This construction does not assert that the supremum is attained. -/
def hilbertHeight (I : TwoSidedIdeal (H →L[𝕜] H)) : Cardinal.{uH} :=
  let _ : BddAbove I.hilbertDimensions := I.bddAbove_hilbertDimensions
  sSup I.hilbertDimensions

/-- Every witnessed dimension is at most the height. -/
theorem le_hilbertHeight_of_mem (I : TwoSidedIdeal (H →L[𝕜] H))
    {d : Cardinal.{uH}} (hd : d ∈ I.hilbertDimensions) : d ≤ I.hilbertHeight :=
  le_csSup I.bddAbove_hilbertDimensions hd

/-- The height satisfies every genuine upper bound of the dimension set. -/
theorem hilbertHeight_le (I : TwoSidedIdeal (H →L[𝕜] H)) {a : Cardinal.{uH}}
    (ha : ∀ d ∈ I.hilbertDimensions, d ≤ a) : I.hilbertHeight ≤ a :=
  csSup_le I.hilbertDimensions_nonempty ha

/-- The height is bounded by any ambient Hilbert basis in the same universe. -/
theorem hilbertHeight_le_mk (I : TwoSidedIdeal (H →L[𝕜] H))
    {ι : Type uH} (bH : HilbertBasis ι 𝕜 H) : I.hilbertHeight ≤ #ι := by
  apply I.hilbertHeight_le
  intro d hd
  simpa only [Cardinal.lift_id] using I.lift_le_of_mem_hilbertDimensions bH hd

/-- Monotonicity of height follows from actual witness inclusion. -/
theorem hilbertHeight_mono {I J : TwoSidedIdeal (H →L[𝕜] H)} (h : I ≤ J) :
    I.hilbertHeight ≤ J.hilbertHeight := by
  apply I.hilbertHeight_le
  intro d hd
  exact J.le_hilbertHeight_of_mem (hilbertDimensions_mono h hd)

/-- The zero ideal has height zero. -/
@[simp]
theorem hilbertHeight_bot :
    (⊥ : TwoSidedIdeal (H →L[𝕜] H)).hilbertHeight = 0 := by
  simp only [hilbertHeight, hilbertDimensions_bot, csSup_singleton]

/-- Attainment (the accessible case of the height) is a separate property. -/
def IsHilbertHeightAttained (I : TwoSidedIdeal (H →L[𝕜] H)) : Prop :=
  I.hilbertHeight ∈ I.hilbertDimensions

/-- The zero height is attained by the zero operator on the zero subspace. -/
theorem isHilbertHeightAttained_bot :
    IsHilbertHeightAttained (⊥ : TwoSidedIdeal (H →L[𝕜] H)) := by
  unfold IsHilbertHeightAttained
  rw [hilbertHeight_bot]
  exact (⊥ : TwoSidedIdeal (H →L[𝕜] H)).zero_mem_hilbertDimensions

end TwoSidedIdeal
