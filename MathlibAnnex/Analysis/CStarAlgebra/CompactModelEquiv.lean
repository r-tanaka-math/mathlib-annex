/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.OperatorSubalgebraIdeal
import MathlibAnnex.Analysis.CStarAlgebra.CompactModel
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Equivalences with the concrete compact-operator algebra

The equivalence uses an already established compact model. Finite-dimensional consequences retain their explicit finite-dimensional hypothesis. No geometric-structure-space classification is used.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Repackage an already proved exact compact model into the actual compact
subtype. The underlying action is the original `pi`, not a new representation. -/
def compactOperatorStarAlgEquiv (pi : NonUnitalCStarRepresentation A H)
    (hpi : IsCompactOperatorModel pi) :
    A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H where
  toFun a := ⟨pi a, hpi.2.1 a⟩
  invFun T := (hpi.2.2 T.val T.property).choose
  left_inv a := hpi.1 (hpi.2.2 (pi a) (hpi.2.1 a)).choose_spec
  right_inv T := Subtype.ext (hpi.2.2 T.val T.property).choose_spec
  map_add' a b := Subtype.ext (map_add pi a b)
  map_mul' a b := Subtype.ext (map_mul pi a b)
  map_star' a := Subtype.ext (map_star pi a)
  map_smul' c a := Subtype.ext (map_smul pi c a)

@[simp]
theorem compactOperatorStarAlgEquiv_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) (a : A) :
    (compactOperatorStarAlgEquiv pi hpi a).val = pi a := rfl

/-- The inverse recovers an actual preimage of each concrete compact operator. -/
theorem compactOperatorStarAlgEquiv_symm_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    pi ((compactOperatorStarAlgEquiv pi hpi).symm T) = T.val := by
  exact congrArg Subtype.val ((compactOperatorStarAlgEquiv pi hpi).apply_symm_apply T)

/-- This norm is the original operator norm on the compact subtype. -/
theorem norm_compactOperatorStarAlgEquiv_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) (a : A) :
    ‖compactOperatorStarAlgEquiv pi hpi a‖ = ‖a‖ := by
  change ‖pi a‖ = ‖a‖
  simpa only [map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry pi hpi.1).dist_eq a 0

/-- Only this finite-dimensional branch uses finite dimension. The nonzero
ideal theorem supplies compact preimages; all operators are compact here. -/
theorem isCompactOperatorModel_of_finiteDimensional_of_image_mul_mem
    [FiniteDimensional ℂ H]
    (pi : NonUnitalCStarRepresentation A H) (hinj : Function.Injective pi)
    (hnz : pi.IsNonzero)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi)) :
    IsCompactOperatorModel pi := by
  refine ⟨hinj, ?_, exists_preimage_compact_of_image_mul_mem pi hinj hnz hmul⟩
  intro a
  exact (pi a).isCompactOperator_of_finiteDimensional_range

/-- Literal equality with the compact star subalgebra in the finite branch. -/
theorem range_eq_compactOperatorStarSubalgebra_of_finiteDimensional_of_mul_mem
    [FiniteDimensional ℂ H]
    (pi : NonUnitalCStarRepresentation A H) (hinj : Function.Injective pi)
    (hnz : pi.IsNonzero)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi)) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  have hmodel := isCompactOperatorModel_of_finiteDimensional_of_image_mul_mem pi hinj hnz hmul
  ext T
  constructor
  · intro hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hT
    exact hmodel.2.1 a
  · intro hT
    exact (NonUnitalStarAlgHom.mem_range pi).2 (hmodel.2.2 T hT)

end MathlibAnnex.Analysis.CStarAlgebra
