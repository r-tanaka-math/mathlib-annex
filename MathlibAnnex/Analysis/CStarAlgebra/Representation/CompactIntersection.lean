/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ComplexExactInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.OperatorSubalgebraIdeal
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorIdeal

/-!
# Compact intersections in irreducible concrete C-star algebras

A norm-closed irreducible operator C-star algebra absorbs arbitrary ambient
multipliers of each of its compact elements. The proof uses finite-rank
operator-norm approximation and the existing norm-controlled exact
self-adjoint interpolation theorem. It does not assume that the finite-rank
approximant belongs to the algebra, that the algebra is unital, or that the
algebra itself is an ambient two-sided ideal.

The actual intersection with the compact operators is then bundled as a
closed two-sided ideal of the ambient bounded-operator algebra. A nonzero
intersection therefore contains every compact operator. This is a direct
alternative to the minimal-projection proof of Blackadar, IV.1.2.4-5.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe v
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Interpolation

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hclosed : IsClosed (S : Set (H →L[ℂ] H)))

include hclosed in
/-- Every ambient left multiplier of a compact member remains in the
irreducible norm-closed operator algebra. -/
theorem left_mul_mem_of_mem_isCompactOperator
    (hS : letI : NonUnitalCStarAlgebra S :=
        NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
      NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    {a : H →L[ℂ] H} (ha : a ∈ S) (hcompact : IsCompactOperator a)
    (b : H →L[ℂ] H) : b * a ∈ S := by
  letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  have hclosure : b * a ∈ closure (S : Set (H →L[ℂ] H)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let C : ℝ := 3 * ‖b‖ + 1
    have hC : 0 < C := by positivity
    obtain ⟨F, hF, hFdist⟩ :=
      hcompact.exists_finiteDimensional_range_norm_sub_lt (div_pos hε hC)
    letI : FiniteDimensional ℂ (LinearMap.range F.toLinearMap) := hF
    obtain ⟨s, hsnorm, hsrange⟩ :=
      exists_norm_le_two_mul_eq_on_range S hclosed hS F b
    have hsF : s.val * F = b * F := by
      ext x
      exact hsrange (F x) ⟨x, rfl⟩
    have hzero : (b - s.val) * F = 0 := by
      rw [sub_mul, ← hsF, sub_self]
    have hrearrange : (b - s.val) * a = (b - s.val) * (a - F) := by
      calc
        (b - s.val) * a = (b - s.val) * ((a - F) + F) := by rw [sub_add_cancel]
        _ = (b - s.val) * (a - F) + (b - s.val) * F := by rw [mul_add]
        _ = (b - s.val) * (a - F) := by rw [hzero, add_zero]
    have hbs : ‖b - s.val‖ ≤ C := by
      calc
        ‖b - s.val‖ ≤ ‖b‖ + ‖s.val‖ := norm_sub_le _ _
        _ ≤ ‖b‖ + 2 * ‖b‖ := add_le_add_right hsnorm ‖b‖
        _ ≤ C := by dsimp [C]; linarith [norm_nonneg b]
    refine ⟨s.val * a, S.mul_mem s.property ha, ?_⟩
    rw [dist_eq_norm, ← sub_mul, hrearrange]
    calc
      ‖(b - s.val) * (a - F)‖ ≤ ‖b - s.val‖ * ‖a - F‖ := norm_mul_le _ _
      _ ≤ C * ‖a - F‖ := mul_le_mul_of_nonneg_right hbs (norm_nonneg _)
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hFdist hC
      _ = ε := by field_simp [ne_of_gt hC]
  rw [hclosed.closure_eq] at hclosure
  exact hclosure

include hclosed in
/-- Every ambient right multiplier of a compact member remains in the
irreducible norm-closed operator algebra. -/
theorem right_mul_mem_of_mem_isCompactOperator
    (hS : letI : NonUnitalCStarAlgebra S :=
        NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
      NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    {a : H →L[ℂ] H} (ha : a ∈ S) (hcompact : IsCompactOperator a)
    (b : H →L[ℂ] H) : a * b ∈ S := by
  have hm : star b * star a ∈ S :=
    left_mul_mem_of_mem_isCompactOperator S hclosed hS (StarMemClass.star_mem ha) hcompact.star (star b)
  have hstar := StarMemClass.star_mem hm
  simpa only [star_mul, star_star] using hstar

end Interpolation

section Ideal

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hclosed : IsClosed (S : Set (H →L[ℂ] H)))
variable (hS : letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

include hclosed hS in
/-- The literal intersection of `S` with the existing compact operators,
bundled as an ambient two-sided ideal. -/
def compactIntersectionIdeal : TwoSidedIdeal (H →L[ℂ] H) :=
  TwoSidedIdeal.mk'
    {a : H →L[ℂ] H | a ∈ S ∧ IsCompactOperator a}
    ⟨S.zero_mem, isCompactOperator_zero⟩
    (fun ha hb => ⟨S.add_mem ha.1 hb.1, ha.2.add hb.2⟩)
    (fun ha => ⟨S.neg_mem ha.1,
      (ContinuousLinearMap.mem_compactOperatorIdeal _).1
        ((ContinuousLinearMap.compactOperatorIdeal ℂ H).neg_mem
          ((ContinuousLinearMap.mem_compactOperatorIdeal _).2 ha.2))⟩)
    (fun {b a} ha =>
      ⟨left_mul_mem_of_mem_isCompactOperator S hclosed hS ha.1 ha.2 b,
        ha.2.clm_comp b⟩)
    (fun {a b} ha =>
      ⟨right_mul_mem_of_mem_isCompactOperator S hclosed hS ha.1 ha.2 b,
        ha.2.comp_clm b⟩)

@[simp]
theorem mem_compactIntersectionIdeal (a : H →L[ℂ] H) :
    a ∈ compactIntersectionIdeal S hclosed hS ↔ a ∈ S ∧ IsCompactOperator a := by
  simp only [compactIntersectionIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

/-- The compact intersection is closed in the original ambient operator norm. -/
theorem isClosed_compactIntersectionIdeal :
    IsClosed (compactIntersectionIdeal S hclosed hS : Set (H →L[ℂ] H)) := by
  have hcarrier : (compactIntersectionIdeal S hclosed hS : Set (H →L[ℂ] H)) =
      {a : H →L[ℂ] H | a ∈ S ∧ IsCompactOperator a} := by
    ext a
    exact mem_compactIntersectionIdeal S hclosed hS a
  rw [hcarrier]
  exact hclosed.inter isClosed_setOf_isCompactOperator

/-- An actual nonzero compact member excludes the zero ideal. -/
theorem compactIntersectionIdeal_ne_bot
    (hnz : ∃ a : H →L[ℂ] H, a ∈ S ∧ IsCompactOperator a ∧ a ≠ 0) :
    compactIntersectionIdeal S hclosed hS ≠ ⊥ := by
  obtain ⟨a, haS, haK, ha0⟩ := hnz
  intro heq
  have ha : a ∈ compactIntersectionIdeal S hclosed hS :=
    (mem_compactIntersectionIdeal S hclosed hS a).2 ⟨haS, haK⟩
  rw [heq, TwoSidedIdeal.mem_bot] at ha
  exact ha0 ha

include hclosed hS in
/-- A nonzero compact intersection forces inclusion of every compact
operator. Only the intersection, not `S` itself, is used as the ambient ideal. -/
theorem compactOperatorStarSubalgebra_le_of_exists_nonzero_compact
    (hnz : ∃ a : H →L[ℂ] H, a ∈ S ∧ IsCompactOperator a ∧ a ≠ 0) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S := by
  have hle : ContinuousLinearMap.compactOperatorIdeal ℂ H ≤
      compactIntersectionIdeal S hclosed hS :=
    (compactIntersectionIdeal S hclosed hS).compactOperatorIdeal_le
      (compactIntersectionIdeal_ne_bot S hclosed hS hnz)
      (isClosed_compactIntersectionIdeal S hclosed hS)
  intro T hT
  have hmem : T ∈ ContinuousLinearMap.compactOperatorIdeal ℂ H :=
    (ContinuousLinearMap.mem_compactOperatorIdeal T).2 hT
  exact (mem_compactIntersectionIdeal S hclosed hS T).1 (hle hmem) |>.1

include hclosed hS in
/-- Blackadar IV.1.2.4, by the direct interpolation route: an irreducible
closed operator C-star algebra contained in the compact operators equals the
whole compact-operator algebra. -/
theorem eq_compactOperatorStarSubalgebra_of_le_of_isIrreducible
    (hle : S ≤ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  obtain ⟨a, ha0⟩ := hS.1
  have haK : IsCompactOperator a.val := hle a.property
  have hnz : ∃ T : H →L[ℂ] H, T ∈ S ∧ IsCompactOperator T ∧ T ≠ 0 := by
    refine ⟨a.val, a.property, haK, ?_⟩
    simpa using ha0
  exact le_antisymm hle
    (compactOperatorStarSubalgebra_le_of_exists_nonzero_compact S hclosed hS hnz)

end Ideal

end MathlibAnnex.Analysis.CStarAlgebra
