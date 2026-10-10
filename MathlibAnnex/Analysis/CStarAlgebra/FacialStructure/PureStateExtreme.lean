/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.PureIrreducible

/-!
# Pure nonunital states as extreme dual functionals

This bridge uses the actual GNS representation of the canonical extension,
restricted back to A, and its actual unit GNS vector. Nonzeroness of the
restricted action follows from the recovered norm-one state. The final
extremality is extremality in the whole dual ball, not just in the state space.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- A pure norm-one positive functional is extreme in the entire dual unit ball. -/
theorem mem_extremePoints_dual_closedBall_of_isPureNonUnitalState
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    phi ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  have hphi : phi ∈ nonUnitalStateSpace A := by
    rw [IsPureNonUnitalState, mem_extremePoints_iff_left] at hpure
    exact hpure.1
  let Phi : StrongDual ℂ (Unitization ℂ A) := unitizationExtension phi
  have hPhi : Phi ∈ stateSpace (Unitization ℂ A) :=
    unitizationExtension_mem_stateSpace phi hphi
  have hPhiPure : IsPureState (Unitization ℂ A) Phi :=
    isPureState_unitizationExtension phi hphi hpure
  let f : Unitization ℂ A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace Phi hPhi
  let xi : f.GNS := stateGNSVector Phi hPhi
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector Phi hPhi
  have hxi0 : xi ≠ 0 := by
    intro hz
    simpa [hz] using hxi
  letI : Nontrivial f.GNS := ⟨⟨xi, 0, hxi0⟩⟩
  let rho : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
  let pi : NonUnitalCStarRepresentation A f.GNS :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hcoeff : NonUnitalCStarRepresentation.matrixCoefficient pi xi xi = phi := by
    ext a
    change inner ℂ (stateGNSVector Phi hPhi)
      ((positiveLinearMapOfMemStateSpace Phi hPhi).gnsStarAlgHom
        (Unitization.inr a) (stateGNSVector Phi hPhi)) = phi a
    rw [inner_gnsStarAlgHom_stateGNSVector]
    exact unitizationExtension_inr phi a
  have hrho : rho.IsIrreducible := by
    apply (Representation.isIrreducible_iff_starAlgHom rho).2
    exact MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom Phi hPhi hPhiPure
  have hnonzero : pi.IsNonzero := by
    change ∃ a : A, pi a ≠ 0
    by_contra! hz
    have hzero : phi = 0 := by
      rw [← hcoeff]
      ext a
      simp only [NonUnitalCStarRepresentation.matrixCoefficient_apply, hz a,
        ContinuousLinearMap.zero_apply, inner_zero_right]
    have hn := hphi.2
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hpi : pi.IsIrreducible :=
    NonUnitalCStarRepresentation.isIrreducible_restriction_of_isIrreducible_unitization
      rho hrho hnonzero
  rw [← hcoeff]
  exact NonUnitalCStarRepresentation.matrixCoefficient_mem_extremePoints_dual_closedBall_of_isIrreducible
    pi hpi xi xi hxi hxi

end MathlibAnnex.Analysis.CStarAlgebra
