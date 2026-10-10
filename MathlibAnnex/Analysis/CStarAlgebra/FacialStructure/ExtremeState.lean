/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitaryTranslate
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PureStateAttainment
import MathlibAnnex.Analysis.Normed.GeometricStructure.ExposedFace
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Positive translates of extreme dual functionals

An extreme dual unit functional has norm one when the original algebra is
nontrivial. Every positive unitary translate is therefore an actual pure
nonunital state, with the existing state-space definition. The existence of
a positive translate is a separate, unresolved part of the polar theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]

/-- Nontriviality is essential: the zero algebra has an extreme zero functional. -/
theorem norm_eq_one_of_mem_extremePoints_dual_closedBall {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ‖rho‖ = 1 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨g, hgnorm, hga⟩ := exists_dual_vector'' ℂ a
  have hg : g ≠ 0 := by
    intro hz
    have hn : (‖a‖ : ℂ) = 0 := by
      rw [hz] at hga
      simpa using hga.symm
    exact ha (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hn))
  have hproper : ({rho} : Set (StrongDual ℂ A)) ≠ closedBall 0 1 := by
    intro h
    have hzero : (0 : StrongDual ℂ A) = rho := by
      apply Set.mem_singleton_iff.mp
      rw [h]
      simp
    have hgrho : g = rho := by
      apply Set.mem_singleton_iff.mp
      rw [h]
      exact mem_closedBall_zero_iff.mpr hgnorm
    exact hg (hgrho.trans hzero.symm)
  have hsphere := NormedSpace.subset_sphere_of_isExtreme_of_ne_closedBall
    (isExtreme_singleton.mpr hrho) hproper (Set.mem_singleton rho)
  simpa only [Metric.mem_sphere, dist_zero_right] using hsphere

variable [PartialOrder A] [StarOrderedRing A]

/-- Positivity, not merely a coefficient representation, promotes an extreme
unit functional to a pure state in the existing nonunital state space. -/
theorem isPureNonUnitalState_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hpositive : ∀ a : A, 0 ≤ a → 0 ≤ rho a) :
    IsPureNonUnitalState A rho := by
  have hnorm := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  rw [IsPureNonUnitalState, mem_extremePoints_iff_left]
  refine ⟨⟨hpositive, hnorm⟩, ?_⟩
  intro f hf g hg hsegment
  exact hrho.2 (mem_closedBall_zero_iff.mpr hf.2.le)
    (mem_closedBall_zero_iff.mpr hg.2.le) hsegment

/-- Any positive unitary translate of an extreme dual functional is pure.
This does not assert the existence of a unitary satisfying the positivity premise. -/
theorem isPureNonUnitalState_unitaryTranslate
    (u : unitary (Unitization ℂ A)) {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hpositive : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate u rho a) :
    IsPureNonUnitalState A (unitaryTranslate u rho) :=
  isPureNonUnitalState_of_mem_extremePoints_dual_closedBall
    (unitaryTranslate_mem_extremePoints_closedBall u hrho) hpositive

/-- Once a positive translate has actually been found, the already proved
pure-state attainment theorem gives a norm-one attainer in the original algebra. -/
theorem exists_norm_eq_one_apply_eq_one_of_nonneg_unitaryTranslate
    (u : unitary (Unitization ℂ A)) {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hpositive : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate u rho a) :
    ∃ a : A, ‖a‖ = 1 ∧ rho a = 1 := by
  obtain ⟨e, _, he, henorm⟩ :=
    exists_nonneg_apply_eq_one_norm_eq_one_of_isPureNonUnitalState
      (unitaryTranslate u rho) (isPureNonUnitalState_unitaryTranslate u hrho hpositive)
  refine ⟨unitizationLeftMul (u : Unitization ℂ A) e, ?_, he⟩
  rw [norm_unitizationLeftMul_unitary, henorm]

end MathlibAnnex.Analysis.CStarAlgebra
