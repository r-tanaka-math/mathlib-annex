/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIntersection

/-!
# The local compact trichotomy for irreducible operator C-star algebras

For an irreducible norm-closed nonunital C-star subalgebra `S` of the
bounded operators on a Hilbert space, exactly one of the following mutually
exclusive geometric positions is available at the local level relevant to
Blackadar IV.1.2.4-5:

* `S` is the compact-operator algebra;
* the compact-operator algebra is properly contained in `S`;
* `S` contains no nonzero compact operator.

The proof packages the literal compact intersection as the ambient closed
two-sided ideal constructed in `CompactIntersection`.  It does not assert
that `S` itself is an ideal in the full bounded-operator algebra.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe v
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hclosed : IsClosed (S : Set (H →L[ℂ] H)))
variable (hS : letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- The ambient compact-intersection ideal is zero exactly when `S` has no
nonzero compact member.  This is an equality of the actual ideal constructed
in `CompactIntersection`, not merely a statement about an auxiliary carrier. -/
theorem compactIntersectionIdeal_eq_bot_iff :
    compactIntersectionIdeal S hclosed hS = ⊥ ↔
      ∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a → a = 0 := by
  constructor
  · intro hbot a haS haK
    have ha : a ∈ compactIntersectionIdeal S hclosed hS :=
      (mem_compactIntersectionIdeal S hclosed hS a).2 ⟨haS, haK⟩
    rw [hbot, TwoSidedIdeal.mem_bot] at ha
    exact ha
  · intro hzero
    apply le_antisymm
    · intro a ha
      rw [TwoSidedIdeal.mem_bot]
      exact hzero a
        ((mem_compactIntersectionIdeal S hclosed hS a).1 ha).1
        ((mem_compactIntersectionIdeal S hclosed hS a).1 ha).2
    · exact bot_le

include hclosed hS in
/-- A nonzero compact member and failure of the reverse compact inclusion
put the compact-operator algebra strictly below `S`. -/
theorem compactOperatorStarSubalgebra_lt_of_exists_nonzero_compact_of_not_le
    (hnz : ∃ a : H →L[ℂ] H, a ∈ S ∧ IsCompactOperator a ∧ a ≠ 0)
    (hnle : ¬ S ≤ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S := by
  have hle : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S :=
    compactOperatorStarSubalgebra_le_of_exists_nonzero_compact S hclosed hS hnz
  exact lt_iff_le_not_ge.mpr ⟨hle, hnle⟩

/-- Local Blackadar trichotomy, stated with the actual compact-intersection
ideal.  The three alternatives are equality with the compact algebra,
proper containment of the compact algebra, or zero compact intersection. -/
theorem eq_compact_or_lt_compact_or_compactIntersectionIdeal_eq_bot :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ∨
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S ∨
      compactIntersectionIdeal S hclosed hS = ⊥ := by
  classical
  by_cases hbot : compactIntersectionIdeal S hclosed hS = ⊥
  · exact Or.inr (Or.inr hbot)
  · have hnzero : ¬ ∀ a : H →L[ℂ] H,
        a ∈ S → IsCompactOperator a → a = 0 := by
      intro hzero
      exact hbot ((compactIntersectionIdeal_eq_bot_iff S hclosed hS).2 hzero)
    push_neg at hnzero
    obtain ⟨a, haS, haK, ha0⟩ := hnzero
    have hnz : ∃ a : H →L[ℂ] H,
        a ∈ S ∧ IsCompactOperator a ∧ a ≠ 0 :=
      ⟨a, haS, haK, ha0⟩
    have hKle : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S :=
      compactOperatorStarSubalgebra_le_of_exists_nonzero_compact S hclosed hS hnz
    by_cases hSle : S ≤ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H
    · exact Or.inl (le_antisymm hSle hKle)
    · exact Or.inr (Or.inl
        (compactOperatorStarSubalgebra_lt_of_exists_nonzero_compact_of_not_le
          S hclosed hS hnz hSle))

include hclosed hS in
/-- Carrier-level form of the local compact trichotomy.  The final case says
literally that every compact member of `S` is zero. -/
theorem eq_compact_or_lt_compact_or_forall_compact_eq_zero :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ∨
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S ∨
      ∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a → a = 0 := by
  rcases eq_compact_or_lt_compact_or_compactIntersectionIdeal_eq_bot
      S hclosed hS with heq | hlt | hbot
  · exact Or.inl heq
  · exact Or.inr (Or.inl hlt)
  · exact Or.inr (Or.inr
      ((compactIntersectionIdeal_eq_bot_iff S hclosed hS).1 hbot))

include hclosed hS in
/-- If all elements of `S` are compact, the third local alternative is
impossible for a nonzero irreducible action, so `S` is exactly the compact
operator algebra. -/
theorem eq_compactOperatorStarSubalgebra_of_forall_isCompactOperator
    (hcompact : ∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a) :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  apply eq_compactOperatorStarSubalgebra_of_le_of_isIrreducible S hclosed hS
  intro a ha
  exact hcompact a ha

end MathlibAnnex.Analysis.CStarAlgebra
