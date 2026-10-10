/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SurjectivePullback
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image

/-!
# Norm equality and extreme-point reflection for surjective C-star pullback

Only existing continuous-linear-map composition is used. The generic
Banach quotient-dual equivalence and its relative weak-star topology are
not redefined here. The image of pullback is deliberately left as its actual
range until that independent annihilator identification is received.
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
variable [PartialOrder B] [StarOrderedRing B]

private noncomputable def normPullbackMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- Norm preservation of the existing precomposition map. Exact
representatives are proved on the C-star side, not assumed of a general
Banach quotient. The zero target is allowed in this norm theorem. -/
theorem norm_comp_of_surjective_starHom
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) (rho : StrongDual ℂ B) :
    ‖rho.comp (normPullbackMap q)‖ = ‖rho‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg rho)
    intro a
    calc
      ‖rho (q a)‖ ≤ ‖rho‖ * ‖q a‖ := rho.le_opNorm _
      _ ≤ ‖rho‖ * ‖a‖ := mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le q a) (norm_nonneg rho)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro b
    obtain ⟨a, ha, han⟩ := exists_preimage_norm_eq_of_surjective q hq b
    calc
      ‖rho b‖ = ‖rho.comp (normPullbackMap q) a‖ := congrArg (fun b : B => ‖rho b‖) ha.symm
      _ ≤ ‖rho.comp (normPullbackMap q)‖ * ‖a‖ :=
        (rho.comp (normPullbackMap q)).le_opNorm a
      _ = ‖rho.comp (normPullbackMap q)‖ * ‖b‖ := by rw [han]

/-- Both extremality directions, with no extra target-ball assumption.
Nontriviality is essential here, unlike in the norm theorem above. -/
theorem comp_mem_extremePoints_dual_closedBall_iff_of_surjective
    [Nontrivial B] (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (rho : StrongDual ℂ B) :
    rho.comp (normPullbackMap q) ∈
        (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ↔
      rho ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ := by
  letI : Nontrivial A := by
    obtain ⟨b, hb⟩ := exists_ne (0 : B)
    obtain ⟨a, ha⟩ := hq b
    refine ⟨⟨a, 0, ?_⟩⟩
    intro hz
    rw [hz, map_zero] at ha
    exact hb ha.symm
  constructor
  · intro h
    apply mem_extremePoints_dual_closedBall_of_comp_of_surjective q hq
    · rw [← norm_comp_of_surjective_starHom q hq rho]
      exact (norm_eq_one_of_mem_extremePoints_dual_closedBall h).le
    · exact h
  · exact comp_mem_extremePoints_dual_closedBall_of_surjective q hq

/-- Exact ambient extreme points in the actual pullback range. Replacing
this range by the entire annihilator is the separate quotient-dual bridge. -/
theorem image_extremePoints_dual_closedBall_of_surjective
    [Nontrivial B] (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    (fun rho : StrongDual ℂ B => rho.comp (normPullbackMap q)) ''
        (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ =
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
        Set.range (fun rho : StrongDual ℂ B => rho.comp (normPullbackMap q)) := by
  ext f
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    exact ⟨comp_mem_extremePoints_dual_closedBall_of_surjective q hq hrho, ⟨rho, rfl⟩⟩
  · rintro ⟨hf, rho, rfl⟩
    exact ⟨rho, (comp_mem_extremePoints_dual_closedBall_iff_of_surjective q hq rho).1 hf, rfl⟩

/-- Kernel transport for every target functional, without extremality or
nontriviality assumptions. The representation kernel is not confused with
this scalar-valued kernel. -/
theorem ker_comp_starHom (q : A →⋆ₙₐ[ℂ] B) (rho : StrongDual ℂ B) :
    (rho.comp (normPullbackMap q)).ker = rho.ker.comap (normPullbackMap q).toLinearMap := by
  ext a
  rfl

end MathlibAnnex.Analysis.CStarAlgebra
