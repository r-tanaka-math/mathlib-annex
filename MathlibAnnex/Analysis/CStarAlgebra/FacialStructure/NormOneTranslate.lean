/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NonUnitalStateGNS
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitCoefficient

/-!
# Norm-one left translates of pure states

The translating element may be any element of the formal unitization, not
necessarily a unitary. Left multiplication is the existing map with values
in the original algebra. Norm one of the resulting functional forces the
actual adjoint-translated GNS target vector to have norm one. In particular
this contains the contraction case of the paper, without a unitary lift.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Multiplication by an arbitrary unitization element acts on coefficient
target vectors by the adjoint. It does not change the source vector. -/
theorem NonUnitalCStarRepresentation.matrixCoefficient_comp_unitizationLeftMul
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (x y : H) (z : Unitization ℂ A) :
    (pi.matrixCoefficient x y).comp (unitizationLeftMul z) =
      pi.matrixCoefficient x (pi.unitization (star z) y) := by
  ext a
  have hmul : pi (unitizationLeftMul z a) = pi.unitization z * pi a := by
    calc
      pi (unitizationLeftMul z a) =
          pi.unitization (unitizationLeftMul z a : Unitization ℂ A) :=
        (pi.unitization_inr _).symm
      _ = pi.unitization z * pi a := by
        rw [inr_unitizationLeftMul, map_mul, pi.unitization_inr]
  change inner ℂ y (pi (unitizationLeftMul z a) x) =
    inner ℂ (pi.unitization (star z) y) (pi a x)
  rw [hmul, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left (pi.unitization z) (pi a x) y).symm

variable [PartialOrder A] [StarOrderedRing A]

/-- A norm-one left translate of a pure state is extreme in the full dual
ball. No contraction assumption on the multiplier is needed for this
stronger form; the resulting functional's norm is explicitly assumed. -/
theorem comp_unitizationLeftMul_mem_extremePoints_dual_closedBall_of_isPure_of_norm_eq_one
    (phi : StrongDual ℂ A) (hphi : IsPureNonUnitalState A phi)
    (z : Unitization ℂ A) (hn : ‖phi.comp (unitizationLeftMul z)‖ = 1) :
    phi.comp (unitizationLeftMul z) ∈
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  let pi := NonUnitalStateGNS.representation phi hphi.1
  let x := NonUnitalStateGNS.vector phi hphi.1
  let y := pi.unitization (star z) x
  have hpi : pi.IsIrreducible :=
    NonUnitalStateGNS.isIrreducible_representation phi hphi.1 hphi
  have hx : ‖x‖ = 1 := NonUnitalStateGNS.norm_vector phi hphi.1
  have heq : pi.matrixCoefficient x y = phi.comp (unitizationLeftMul z) := by
    rw [← pi.matrixCoefficient_comp_unitizationLeftMul]
    exact congrArg (fun f : StrongDual ℂ A => f.comp (unitizationLeftMul z))
      (NonUnitalStateGNS.matrixCoefficient_representation phi hphi.1)
  have hy : ‖y‖ = 1 := by
    have hnorm := pi.norm_matrixCoefficient_of_isIrreducible hpi x y
    rw [hx, one_mul, heq, hn] at hnorm
    exact hnorm.symm
  rw [← heq]
  exact pi.matrixCoefficient_mem_extremePoints_dual_closedBall_of_isIrreducible hpi x y hx hy

end MathlibAnnex.Analysis.CStarAlgebra
