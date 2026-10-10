/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientLinear
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.ExtremeKernel
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitCoefficient

/-!
# Irreducible coefficient kernels as actual GSS points

Both vectors may have any nonzero norm. Normalizing them multiplies the
functional by a nonzero scalar, hence leaves its actual kernel unchanged.
All equality statements below compare points of the received general GSS,
not a new space of coefficient labels.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A coefficient of two nonzero vectors gives a genuine point of S(A). -/
theorem ker_matrixCoefficient_mem_geometricStructureFamily
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((matrixCoefficient pi x y).ker : Set A) ∈ NormedSpace.geometricStructureFamily ℂ A := by
  obtain ⟨x', y', hx', hy', hker⟩ := exists_unit_vectors_ker_matrixCoefficient_eq pi x y hx hy
  apply (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall _).2
  exact ⟨matrixCoefficient pi x' y',
    matrixCoefficient_mem_extremePoints_dual_closedBall_of_isIrreducible pi hpi x' y' hx' hy',
    congrArg (fun P : Submodule ℂ A => (P : Set A)) hker⟩

/-- The kernel point of a nonzero irreducible matrix coefficient. -/
def matrixCoefficientKernel (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) : NormedSpace.GeometricStructureSpace ℂ A :=
  ⟨(matrixCoefficient pi x y).ker,
    ker_matrixCoefficient_mem_geometricStructureFamily pi hpi x y hx hy⟩

@[simp]
theorem coe_matrixCoefficientKernel (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficientKernel pi hpi x y hx hy).val = ((matrixCoefficient pi x y).ker : Set A) := rfl

/-- Equality of actual GSS kernel points is equality of the target lines. -/
theorem matrixCoefficientKernel_eq_iff_span_eq_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z : H) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    matrixCoefficientKernel pi hpi x y hx hy = matrixCoefficientKernel pi hpi x z hx hz ↔
      Submodule.span ℂ {y} = Submodule.span ℂ {z} := by
  constructor
  · intro h
    apply (ker_matrixCoefficient_eq_iff_span_eq_right pi hpi hx hy hz).1
    exact SetLike.coe_injective (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact congrArg (fun P : Submodule ℂ A => (P : Set A))
      ((ker_matrixCoefficient_eq_iff_span_eq_right pi hpi hx hy hz).2 h)

/-- Equality of actual GSS kernel points is equality of the source lines. -/
theorem matrixCoefficientKernel_eq_iff_span_eq_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x z y : H) (hx : x ≠ 0) (hz : z ≠ 0) (hy : y ≠ 0) :
    matrixCoefficientKernel pi hpi x y hx hy = matrixCoefficientKernel pi hpi z y hz hy ↔
      Submodule.span ℂ {x} = Submodule.span ℂ {z} := by
  constructor
  · intro h
    apply (ker_matrixCoefficient_eq_iff_span_eq_left pi hpi hx hz hy).1
    exact SetLike.coe_injective (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact congrArg (fun P : Submodule ℂ A => (P : Set A))
      ((ker_matrixCoefficient_eq_iff_span_eq_left pi hpi hx hz hy).2 h)

variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual unitary intertwiners identify the represented kernel points exactly. -/
theorem matrixCoefficientKernel_eq_of_intertwines
    (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hrho : rho.IsIrreducible)
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ a x, U (pi a x) = rho a (U x))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    matrixCoefficientKernel rho hrho (U x) (U y)
      (fun h => hx (U.injective (h.trans (map_zero U).symm)))
      (fun h => hy (U.injective (h.trans (map_zero U).symm))) =
        matrixCoefficientKernel pi hpi x y hx hy := by
  apply Subtype.ext
  change ((matrixCoefficient rho (U x) (U y)).ker : Set A) =
    ((matrixCoefficient pi x y).ker : Set A)
  rw [matrixCoefficient_eq_of_intertwines pi rho U hU]

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
