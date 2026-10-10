/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.RankOneRelations
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FiniteCoefficientRelations
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientKernel
import Mathlib.Data.Fintype.Option

/-!
# Both projective lines of an irreducible coefficient kernel

The received finite-relation/WOT theorem moves equalities to the full operator
space before rank-one tests are used. This is not an assumption that the
representation contains rank-one operators. All vectors in the linear-relation
lemmas may be zero; projective uniqueness requires the four stated nonzero
conditions, but no unit normalization, faithfulness, or finite dimension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual finite WOT relation theorem also transfers an inhomogeneous
finite equality, with all scalar factors in the source slot. -/
theorem matrixCoefficient_eq_sum_smul_iff_operator
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {ι : Type*} [Fintype ι] (x y : ι → H) (z w : H) (c : ι → ℂ) :
    matrixCoefficient pi z w = ∑ i, c i • matrixCoefficient pi (x i) (y i) ↔
      InnerProductSpace.matrixCoefficient ℂ z w =
        ∑ i, c i • InnerProductSpace.matrixCoefficient ℂ (x i) (y i) := by
  classical
  let X : Option ι → H := Option.elim' (-z) (fun i => c i • x i)
  let Y : Option ι → H := Option.elim' w y
  have hzero := sum_matrixCoefficient_eq_zero_iff_sum_operator_matrixCoefficient_eq_zero
    pi hpi X Y
  simpa [X, Y, Fintype.sum_option,
    matrixCoefficient_neg_left, matrixCoefficient_smul_left,
    InnerProductSpace.matrixCoefficient_neg_left,
    InnerProductSpace.matrixCoefficient_smul_left, _root_.neg_add_eq_zero] using hzero

/-- A single scalar equality is transferred with its scalar unchanged. -/
theorem matrixCoefficient_eq_smul_iff_operator
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z w : H) (c : ℂ) :
    matrixCoefficient pi z w = c • matrixCoefficient pi x y ↔
      InnerProductSpace.matrixCoefficient ℂ z w =
        c • InnerProductSpace.matrixCoefficient ℂ x y := by
  simpa using matrixCoefficient_eq_sum_smul_iff_operator pi hpi
    (fun _ : Unit => x) (fun _ : Unit => y) z w (fun _ => c)

/-- General two-pair kernel equality, without assuming a common vector. -/
theorem ker_matrixCoefficient_eq_iff_span_eq_and_span_eq
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x₁ x₂ y₁ y₂ : H} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    (matrixCoefficient pi x₁ y₁).ker = (matrixCoefficient pi x₂ y₂).ker ↔
      Submodule.span ℂ {x₁} = Submodule.span ℂ {x₂} ∧
      Submodule.span ℂ {y₁} = Submodule.span ℂ {y₂} := by
  constructor
  · intro hk
    obtain ⟨c, _, hc⟩ := (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
      ((matrixCoefficient_ne_zero_iff pi hpi x₁ y₁).2 ⟨hx₁, hy₁⟩)).mp hk
    exact InnerProductSpace.span_eq_and_span_eq_of_matrixCoefficient_eq_smul
      hx₁ hy₁ hx₂ hy₂ ((matrixCoefficient_eq_smul_iff_operator
        pi hpi x₁ y₁ x₂ y₂ c).mp hc)
  · rintro ⟨hx, hy⟩
    exact ((ker_matrixCoefficient_eq_iff_span_eq_left pi hpi hx₁ hx₂ hy₁).mpr hx).trans
      ((ker_matrixCoefficient_eq_iff_span_eq_right pi hpi hx₂ hy₁ hy₂).mpr hy)

/-- The two-independent-lines obstruction, now for the original algebra. -/
theorem eq_zero_or_eq_zero_of_matrixCoefficient_eq_smul_add_smul
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x₁ x₂ y₁ y₂ z w : H} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hx : Submodule.span ℂ {x₁} ≠ Submodule.span ℂ {x₂})
    (hy : Submodule.span ℂ {y₁} ≠ Submodule.span ℂ {y₂}) {a b : ℂ}
    (h : matrixCoefficient pi z w =
      a • matrixCoefficient pi x₁ y₁ + b • matrixCoefficient pi x₂ y₂) :
    a = 0 ∨ b = 0 := by
  have hh : InnerProductSpace.matrixCoefficient ℂ z w =
      a • InnerProductSpace.matrixCoefficient ℂ x₁ y₁ +
      b • InnerProductSpace.matrixCoefficient ℂ x₂ y₂ := by
    have h' : matrixCoefficient pi z w =
        ∑ i : Fin 2, (![a, b] i) • matrixCoefficient pi (![x₁, x₂] i) (![y₁, y₂] i) := by
      simpa [Fin.sum_univ_two] using h
    simpa using (matrixCoefficient_eq_sum_smul_iff_operator pi hpi
      ![x₁, x₂] ![y₁, y₂] z w ![a, b]).mp h'
  exact InnerProductSpace.eq_zero_or_eq_zero_of_matrixCoefficient_eq_smul_add_smul
    hx₁ hx₂ hy₁ hy₂ hx hy hh

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
