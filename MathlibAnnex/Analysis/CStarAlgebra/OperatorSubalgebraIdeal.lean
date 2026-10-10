/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Operator subalgebras absorbing ambient multipliers

Actual two-sided ideal carriers and compact preimages. These constructions do not use geometric structure spaces.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundle both actual multiplier laws on a literal operator subalgebra.
Neither a unit in the subalgebra nor norm closedness is needed to form the ideal. -/
def operatorIdealOfMulMem (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S) :
    TwoSidedIdeal (H →L[ℂ] H) :=
  TwoSidedIdeal.mk' (S : Set (H →L[ℂ] H)) S.zero_mem
    (fun ha hb => S.add_mem ha hb) (fun ha => S.neg_mem ha)
    (fun {b a} ha => (hS b a ha).1)
    (fun {a b} ha => (hS b a ha).2)

@[simp]
theorem mem_operatorIdealOfMulMem
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S)
    (a : H →L[ℂ] H) : a ∈ operatorIdealOfMulMem S hS ↔ a ∈ S := by
  simp only [operatorIdealOfMulMem, TwoSidedIdeal.mem_mk']
  rfl

/-- This is an equality of carriers in the original operator-norm space. -/
theorem coe_operatorIdealOfMulMem
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S) :
    (operatorIdealOfMulMem S hS : Set (H →L[ℂ] H)) = S := by
  ext a
  exact mem_operatorIdealOfMulMem S hS a

theorem isClosed_operatorIdealOfMulMem
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S)
    (hclosed : IsClosed (S : Set (H →L[ℂ] H))) :
    IsClosed (operatorIdealOfMulMem S hS : Set (H →L[ℂ] H)) := by
  rw [coe_operatorIdealOfMulMem]
  exact hclosed

/-- The zero ideal is excluded by an actual nonzero member. -/
theorem operatorIdealOfMulMem_ne_bot
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S)
    (hnz : ∃ a : H →L[ℂ] H, a ∈ S ∧ a ≠ 0) :
    operatorIdealOfMulMem S hS ≠ ⊥ := by
  obtain ⟨a, ha, ha0⟩ := hnz
  intro heq
  have hm := (mem_operatorIdealOfMulMem S hS a).2 ha
  rw [heq, TwoSidedIdeal.mem_bot] at hm
  exact ha0 hm


/-- Compact inclusion is a consequence of the proved multiplier laws and
norm closedness, not a new premise. -/
theorem compactOperatorStarSubalgebra_le_of_mul_mem
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hS : ∀ (b a : H →L[ℂ] H), a ∈ S → b * a ∈ S ∧ a * b ∈ S)
    (hclosed : IsClosed (S : Set (H →L[ℂ] H)))
    (hnz : ∃ a : H →L[ℂ] H, a ∈ S ∧ a ≠ 0) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S := by
  intro a ha
  apply (mem_operatorIdealOfMulMem S hS a).1
  exact (operatorIdealOfMulMem S hS).mem_of_isCompactOperator
    (operatorIdealOfMulMem_ne_bot S hS hnz)
    (isClosed_operatorIdealOfMulMem S hS hclosed) ha

section Representation

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Every compact has an actual preimage under the same representation.
Faithfulness supplies closedness via the existing C-star isometry theorem. -/
theorem exists_preimage_compact_of_image_mul_mem
    (pi : NonUnitalCStarRepresentation A H) (hinj : Function.Injective pi)
    (hnz : pi.IsNonzero)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi))
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    ∃ a : A, pi a = T := by
  have hclosed : IsClosed ((NonUnitalStarAlgHom.range pi) : Set (H →L[ℂ] H)) := by
    change IsClosed (Set.range pi)
    exact (NonUnitalStarAlgHom.isometry pi hinj).isClosedEmbedding.isClosed_range
  have hrange : ∃ a : H →L[ℂ] H, a ∈ (NonUnitalStarAlgHom.range pi) ∧ a ≠ 0 := by
    obtain ⟨a, ha⟩ := hnz
    exact ⟨pi a, (NonUnitalStarAlgHom.mem_range pi).2 ⟨a, rfl⟩, ha⟩
  exact (NonUnitalStarAlgHom.mem_range pi).1
    (compactOperatorStarSubalgebra_le_of_mul_mem (NonUnitalStarAlgHom.range pi) hmul hclosed hrange hT)

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
