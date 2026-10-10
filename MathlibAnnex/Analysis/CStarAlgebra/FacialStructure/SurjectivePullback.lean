/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitCoefficient

/-!
# Extreme dual functionals under a surjective C-star homomorphism

The target must be nontrivial: the zero functional is extreme in the dual
ball of the zero algebra, but its pullback is not extreme in a nontrivial
domain. The forward proof uses a real irreducible coefficient realization,
not a quotient unitary lift or a minimal-unitization identification.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B] [Nontrivial B]

private noncomputable def surjectivePullbackMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- An arbitrary extreme functional of the target pulls back to an extreme
functional of the whole domain dual ball. -/
theorem comp_mem_extremePoints_dual_closedBall_of_surjective
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    {rho : StrongDual ℂ B}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ) :
    rho.comp (surjectivePullbackMap q) ∈
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  have hn : ‖rho‖ = 1 := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  have hne : rho ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  let pi := NonUnitalFunctional.cyclicRepresentation rho hne
  let x := NonUnitalFunctional.cyclicSourceVector rho hne
  let y := NonUnitalFunctional.cyclicTargetVector rho hne
  have hpi : pi.IsIrreducible :=
    NonUnitalFunctional.isIrreducible_cyclicRepresentation rho hne hrho
  have hx : ‖x‖ = 1 := NonUnitalFunctional.norm_cyclicSourceVector rho hne
  have hy : ‖y‖ = 1 := NonUnitalFunctional.norm_cyclicTargetVector rho hne
  have hrec : NonUnitalCStarRepresentation.matrixCoefficient pi x y = rho :=
    NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one rho hne hn
  have hcomp : NonUnitalCStarRepresentation.IsIrreducible (pi.comp q) :=
    (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective pi q hq).2 hpi
  have hext :=
    NonUnitalCStarRepresentation.matrixCoefficient_mem_extremePoints_dual_closedBall_of_isIrreducible
      (pi.comp q) hcomp x y hx hy
  rwa [NonUnitalCStarRepresentation.matrixCoefficient_comp, hrec] at hext

/-- Reflection of extremality for a target functional already in its unit
ball. Norm equality will remove this explicit ball condition once the
quotient-norm bridge has been supplied. -/
theorem mem_extremePoints_dual_closedBall_of_comp_of_surjective
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    {rho : StrongDual ℂ B} (hn : ‖rho‖ ≤ 1)
    (hrho : rho.comp (surjectivePullbackMap q) ∈
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    rho ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left] at hrho ⊢
  refine ⟨mem_closedBall_zero_iff.mpr hn, ?_⟩
  have hball (f : StrongDual ℂ B) (hf : f ∈ closedBall 0 1) :
      f.comp (surjectivePullbackMap q) ∈ closedBall 0 1 := by
    apply mem_closedBall_zero_iff.mpr
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    calc
      ‖f (q a)‖ ≤ ‖f‖ * ‖q a‖ := f.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul (mem_closedBall_zero_iff.mp hf)
        (NonUnitalStarAlgHom.norm_apply_le q a) (norm_nonneg _) zero_le_one
  intro f hf g hg hseg
  obtain ⟨s, t, hs, ht, hst, hfg⟩ := hseg
  have hlin : s • f.comp (surjectivePullbackMap q) + t • g.comp (surjectivePullbackMap q) =
      rho.comp (surjectivePullbackMap q) := by
    ext a
    exact congrArg (fun k : StrongDual ℂ B => k (q a)) hfg
  have heq := hrho.2 _ (hball f hf) _ (hball g hg) ⟨s, t, hs, ht, hst, hlin⟩
  ext b
  obtain ⟨a, rfl⟩ := hq b
  exact congrArg (fun k : StrongDual ℂ A => k a) heq

end MathlibAnnex.Analysis.CStarAlgebra
