/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisRangeCardinality
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinalNets
import MathlibAnnex.Analysis.InnerProductSpace.CardinalCompactAdjoint
import Mathlib.Tactic

/-!
# Operators with a strictly small norm-closed Hilbert range

`HasSmallHilbertRange α T` is defined independently of bounded-image cardinal
compactness. It asks for an actual Hilbert basis of the norm closure of the
range, with index cardinal strictly below `α`. The basis is existential, so the
predicate is not vacuous in the absence of a basis. No new Hilbert-dimension
function is introduced. The submodule and two-sided ideal carry the original
operator norm. General norm closedness is deliberately not asserted.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped Cardinal Topology

universe uF uH uK uG uI uA
variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The norm closure of the actual range has a Hilbert basis of strictly
smaller cardinality than `α`. This is not the bounded-image definition. -/
def HasSmallHilbertRange (α : Cardinal.{uA}) (T : H →L[𝕜] K) : Prop :=
  ∃ (ι : Type uK) (b : HilbertBasis ι 𝕜 T.range.topologicalClosure),
    Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uK} α

namespace HasSmallHilbertRange

variable {α β : Cardinal.{uA}} {T : H →L[𝕜] K}

/-- The strict bound is independent of the chosen Hilbert basis and its universe. -/
theorem hilbertBasis_lift_mk_lt (hT : HasSmallHilbertRange α T)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 T.range.topologicalClosure) :
    Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α := by
  obtain ⟨κ, c, hc⟩ := hT
  exact c.lift_mk_lt_of_denseRange b (.id 𝕜 T.range.topologicalClosure)
    (fun y => subset_closure ⟨y, rfl⟩) hc

/-- Monotonicity concerns the cardinal bound, not a change of the range. -/
theorem mono_cardinal (hT : HasSmallHilbertRange α T) (hαβ : α ≤ β) :
    HasSmallHilbertRange β T := by
  obtain ⟨ι, b, hb⟩ := hT
  exact ⟨ι, b, hb.trans_le (Cardinal.lift_le.mpr hαβ)⟩

/-- Strictly small closed range implies the existing bounded-image condition.
Only bounded subsets of that closed range are supplied with nets. -/
theorem isCardinalCompactOperator (hT : HasSmallHilbertRange α T)
    (hα : Cardinal.aleph0 ≤ α) : IsCardinalCompactOperator α T := by
  obtain ⟨ι, b, hb⟩ := hT
  intro B hB
  have hp : Bornology.IsBounded (T.toClosureRange '' B) :=
    T.toClosureRange.lipschitz.isBounded_image hB
  have hn := (b.cardinalTotallyBounded_of_isBounded hα hb hp).image
    T.range.topologicalClosure.subtypeL.uniformContinuous
  have heq : T.range.topologicalClosure.subtypeL '' (T.toClosureRange '' B) = T '' B := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨T.toClosureRange x, ⟨x, hx, rfl⟩, rfl⟩
  simpa only [heq] using hn

end HasSmallHilbertRange

namespace ContinuousLinearMap

/-- A small closed subspace containing the literal range is sufficient. The
projection used in the proof is surjective onto the smaller closed range. -/
theorem hasSmallHilbertRange_of_range_le [CompleteSpace K]
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (M : Submodule 𝕜 K)
    (hM : IsClosed (M : Set K)) (hTM : T.range ≤ M)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 M)
    (hb : Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α) :
    HasSmallHilbertRange α T := by
  let N := T.range.topologicalClosure
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := T.range.isClosed_topologicalClosure.completeSpace_coe
  have hNM : N ≤ M := Submodule.topologicalClosure_minimal _ hTM hM
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 N
  let q : M →L[𝕜] N := N.orthogonalProjectionOnto.comp M.subtypeL
  have hq : Surjective q := by
    intro y
    refine ⟨⟨(y : K), hNM y.property⟩, ?_⟩
    change N.orthogonalProjectionOnto (y : K) = y
    exact N.orthogonalProjectionOnto_mem_subspace_eq_self y
  exact ⟨κ, c, b.lift_mk_lt_of_denseRange c q hq.denseRange hb⟩

/-- The zero operator has zero-dimensional closed range. A positive cardinal
bound is still required; this is not a claim at cardinal zero. -/
theorem hasSmallHilbertRange_zero [CompleteSpace K] {α : Cardinal.{uA}}
    (hα : 0 < α) : HasSmallHilbertRange α (0 : H →L[𝕜] K) := by
  let N := (0 : H →L[𝕜] K).range.topologicalClosure
  letI : CompleteSpace N := (0 : H →L[𝕜] K).range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 N
  have hi : IsEmpty ι := ⟨fun i => b.orthonormal.linearIndependent.ne_zero i
    (Subtype.ext (by simpa [N] using (b i).property))⟩
  letI : IsEmpty ι := hi
  refine ⟨ι, b, ?_⟩
  have h : (0 : Cardinal.{max uK uA}) < Cardinal.lift.{uK} α :=
    by simpa only [Cardinal.lift_zero] using (Cardinal.lift_lt.mpr hα :
      Cardinal.lift.{uK} 0 < Cardinal.lift.{uK} α)
  simpa only [Cardinal.mk_eq_zero, Cardinal.lift_zero] using h

end ContinuousLinearMap

namespace HasSmallHilbertRange

variable {α : Cardinal.{uA}} {T S : H →L[𝕜] K}

/-- Monotonicity under inclusion of literal ranges. -/
theorem of_range_le [CompleteSpace K]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {A : G →L[𝕜] K} (hT : HasSmallHilbertRange α T)
    (hAT : A.range ≤ T.range) : HasSmallHilbertRange α A := by
  obtain ⟨ι, b, hb⟩ := hT
  exact A.hasSmallHilbertRange_of_range_le T.range.topologicalClosure
    T.range.isClosed_topologicalClosure (hAT.trans T.range.le_topologicalClosure) b hb

/-- Precomposition does not enlarge the range. -/
theorem comp_right [CompleteSpace K]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (hT : HasSmallHilbertRange α T) (U : G →L[𝕜] H) :
    HasSmallHilbertRange α (T.comp U) := by
  apply hT.of_range_le
  rintro y ⟨x, rfl⟩
  exact ⟨U x, rfl⟩

/-- Postcomposition cannot increase the dimension of the closed range. The
intermediate map has dense range only, as recorded in the cardinality theorem. -/
theorem comp_left [CompleteSpace K]
    {G : Type uG} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (hT : HasSmallHilbertRange α T) (U : K →L[𝕜] G) :
    HasSmallHilbertRange α (U.comp T) := by
  obtain ⟨ι, b, hb⟩ := hT
  let q : T.range.topologicalClosure →L[𝕜] G := U.comp T.range.topologicalClosure.subtypeL
  let N := q.range.topologicalClosure
  letI : CompleteSpace N := q.range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 N
  have hc := b.lift_mk_lt_of_denseRange c q.toClosureRange q.denseRange_toClosureRange hb
  apply (U.comp T).hasSmallHilbertRange_of_range_le N q.range.isClosed_topologicalClosure ?_ c hc
  rintro y ⟨x, rfl⟩
  exact q.range.le_topologicalClosure ⟨T.toClosureRange x, rfl⟩

/-- Scalar multiplication preserves the same closed-range bound, including scalar zero. -/
theorem smul [CompleteSpace K] (hT : HasSmallHilbertRange α T) (c : 𝕜) :
    HasSmallHilbertRange α (c • T) := by
  apply hT.of_range_le
  rintro y ⟨x, rfl⟩
  exact ⟨c • x, by change T (c • x) = c • T x; exact map_smul T c x⟩

/-- Addition uses one finite union of basis families. No countable union of
individually small cardinal bounds is invoked. -/
theorem add [CompleteSpace K] (hT : HasSmallHilbertRange α T)
    (hS : HasSmallHilbertRange α S) (hα : Cardinal.aleph0 ≤ α) :
    HasSmallHilbertRange α (T + S) := by
  classical
  obtain ⟨ι, b, hb⟩ := hT
  obtain ⟨κ, c, hc⟩ := hS
  let v : ι ⊕ κ → K := Sum.elim (fun i => (b i : K)) (fun j => (c j : K))
  let N := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
  have hN : IsClosed (N : Set K) := (Submodule.span 𝕜 (Set.range v)).isClosed_topologicalClosure
  letI : CompleteSpace N := hN.completeSpace_coe
  obtain ⟨ν, d, -⟩ := exists_hilbertBasis 𝕜 N
  have hn : Cardinal.lift.{uA} (#ν) < Cardinal.lift.{uK} α := by
    have hle : #ν ≤ #(ι ⊕ κ) := by
      simpa only [Cardinal.lift_id] using HilbertBasis.lift_mk_le_closed_span v d
    have hsum : Cardinal.lift.{uA} (#(ι ⊕ κ)) < Cardinal.lift.{uK} α := by
      simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_add]
      exact Cardinal.add_lt_of_lt (by simpa only [Cardinal.lift_aleph0] using
        (Cardinal.lift_le.mpr hα : Cardinal.lift.{uK} Cardinal.aleph0 ≤ Cardinal.lift.{uK} α)) hb hc
    exact (Cardinal.lift_le.mpr hle).trans_lt hsum
  have hTN : T.range.topologicalClosure ≤ N :=
    b.submodule_le_of_forall_mem hN (fun i =>
      (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
  have hSN : S.range.topologicalClosure ≤ N :=
    c.submodule_le_of_forall_mem hN (fun i =>
      (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  apply (T + S).hasSmallHilbertRange_of_range_le N hN ?_ d hn
  rintro y ⟨x, rfl⟩
  exact N.add_mem (hTN (T.range.le_topologicalClosure (T.mem_range_self x)))
    (hSN (S.range.le_topologicalClosure (S.mem_range_self x)))

/-- Negation is scalar multiplication by minus one. -/
theorem neg [CompleteSpace K] (hT : HasSmallHilbertRange α T) :
    HasSmallHilbertRange α (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1)

end HasSmallHilbertRange

namespace ContinuousLinearMap

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [CompleteSpace K]

/-- Adjoint preserves a strict bound on the closed-range Hilbert dimension. -/
theorem hasSmallHilbertRange_adjoint {α : Cardinal.{uA}} {T : H →L[𝕜] K}
    (hT : HasSmallHilbertRange α T) : HasSmallHilbertRange α T.adjoint := by
  obtain ⟨ι, b, hb⟩ := hT
  letI : CompleteSpace T.adjoint.range.topologicalClosure :=
    T.adjoint.range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 T.adjoint.range.topologicalClosure
  have hq_exists : ∃ q : T.range.topologicalClosure →L[𝕜]
      T.adjoint.range.topologicalClosure, DenseRange q := by
    have h : ∃ q : T.adjoint.adjoint.range.topologicalClosure →L[𝕜]
        T.adjoint.range.topologicalClosure, DenseRange q :=
      ⟨T.adjoint.adjointClosureRangeRestriction,
        T.adjoint.denseRange_adjointClosureRangeRestriction⟩
    rw [adjoint_adjoint] at h
    exact h
  obtain ⟨q, hq⟩ := hq_exists
  exact ⟨κ, c, b.lift_mk_lt_of_denseRange c q hq hb⟩

/-- Adjoint preserves and reflects every strict closed-range dimension bound. -/
theorem hasSmallHilbertRange_adjoint_iff (T : H →L[𝕜] K) (α : Cardinal.{uA}) :
    HasSmallHilbertRange α T.adjoint ↔ HasSmallHilbertRange α T := by
  exact ⟨fun h => by simpa only [adjoint_adjoint] using hasSmallHilbertRange_adjoint h,
    hasSmallHilbertRange_adjoint⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable (𝕜 H K) [CompleteSpace K]

/-- The small-closed-range operators form a submodule for infinite bounds.
It is not claimed to be norm closed. -/
def cardinalRangeOperator (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    Submodule 𝕜 (H →L[𝕜] K) where
  carrier := {T | HasSmallHilbertRange α T}
  zero_mem' := hasSmallHilbertRange_zero (lt_of_lt_of_le Cardinal.aleph0_pos hα)
  add_mem' := fun hT hS => hT.add hS hα
  smul_mem' := fun c _ hT => hT.smul c

@[simp]
theorem mem_cardinalRangeOperator (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α)
    (T : H →L[𝕜] K) : T ∈ cardinalRangeOperator 𝕜 H K α hα ↔
      HasSmallHilbertRange α T := Iff.rfl

/-- The inherited norm is exactly the ambient operator norm. -/
theorem norm_cardinalRangeOperator (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α)
    (T : cardinalRangeOperator 𝕜 H K α hα) : ‖T‖ = ‖(T : H →L[𝕜] K)‖ := rfl

variable {𝕜 H K}

/-- Inclusion in the already defined bounded-image submodule. -/
theorem cardinalRangeOperator_le_cardinalCompactOperator (α : Cardinal.{uA})
    (hα : Cardinal.aleph0 ≤ α) : cardinalRangeOperator 𝕜 H K α hα ≤
      cardinalCompactOperator (E := H) (F := K) α (RingHom.id 𝕜) hα := by
  intro T hT
  exact hT.isCardinalCompactOperator hα

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The algebraic two-sided ideal of small closed ranges. No closedness field
or completion is inserted into this construction. -/
def cardinalRangeOperatorIdeal (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    TwoSidedIdeal (H →L[𝕜] H) :=
  TwoSidedIdeal.mk' {T | HasSmallHilbertRange α T}
    (hasSmallHilbertRange_zero (lt_of_lt_of_le Cardinal.aleph0_pos hα))
    (fun {T S} hT hS => hT.add hS hα)
    (fun {T} hT => hT.neg)
    (fun {T S} hS => hS.comp_left T)
    (fun {T S} hT => hT.comp_right S)

@[simp]
theorem mem_cardinalRangeOperatorIdeal (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α)
    (T : H →L[𝕜] H) : T ∈ cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H) α hα ↔
      HasSmallHilbertRange α T := by
  simp only [cardinalRangeOperatorIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

/-- Algebraic ideal and submodule have precisely the same carrier. -/
theorem coe_cardinalRangeOperatorIdeal (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    (cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H) α hα : Set (H →L[𝕜] H)) =
      (cardinalRangeOperator 𝕜 H H α hα : Set (H →L[𝕜] H)) := by
  ext T
  exact mem_cardinalRangeOperatorIdeal α hα T

/-- Star closedness is membership preservation by the actual adjoint. -/
theorem star_mem_cardinalRangeOperatorIdeal_iff (α : Cardinal.{uA})
    (hα : Cardinal.aleph0 ≤ α) (T : H →L[𝕜] H) :
    star T ∈ cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H) α hα ↔
      T ∈ cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H) α hα := by
  simp only [mem_cardinalRangeOperatorIdeal, star_eq_adjoint]
  exact hasSmallHilbertRange_adjoint_iff T α

/-- Inclusion of the literal ideals, retaining the infinite-cardinal hypothesis. -/
theorem cardinalRangeOperatorIdeal_le_cardinalCompactOperatorIdeal
    (α : Cardinal.{uA}) (hα : Cardinal.aleph0 ≤ α) :
    cardinalRangeOperatorIdeal (𝕜 := 𝕜) (H := H) α hα ≤
      cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := H) α hα := by
  intro T hT
  exact (mem_cardinalCompactOperatorIdeal α hα T).mpr
    (((mem_cardinalRangeOperatorIdeal α hα T).mp hT).isCardinalCompactOperator hα)

end ContinuousLinearMap
