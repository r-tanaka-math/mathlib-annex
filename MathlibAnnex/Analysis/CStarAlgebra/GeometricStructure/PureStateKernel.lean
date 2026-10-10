/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PureStateExtreme
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.ExtremeKernel

/-!
# Pure-state translates in the original geometric structure space

Paper 5.3 is obtained from the received extreme-kernel family theorem and
Notes 11.9 in one direction, and genuine pure-state dual extremality in the
other. The parametrization uses actual subsets of A, so different phases
with the same kernel do not create different GSS points.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

/-- Paper 5.3: the original S(A) is the family of pure-state translate kernels. -/
theorem geometricStructureFamily_eq_setOf_exists_pureState_unitaryTranslate :
    NormedSpace.geometricStructureFamily ℂ A =
      {I : Set A | ∃ phi : StrongDual ℂ A, IsPureNonUnitalState A phi ∧
        ∃ u : unitary (Unitization ℂ A), ((unitaryTranslate u phi).ker : Set A) = I} := by
  ext I
  rw [mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall]
  constructor
  · rintro ⟨rho, hrho, hI⟩
    obtain ⟨phi, hphi, u, _, hrep⟩ :=
      exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall hrho
    exact ⟨phi, hphi, star u, hrep ▸ hI⟩
  · rintro ⟨phi, hphi, u, hI⟩
    refine ⟨unitaryTranslate u phi, ?_, hI⟩
    exact unitaryTranslate_mem_extremePoints_closedBall u
      (mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hphi)

/-- A pure-state translate kernel as a point of the existing general GSS. -/
def pureStateTranslateKernel (phi : StrongDual ℂ A)
    (hphi : IsPureNonUnitalState A phi) (u : unitary (Unitization ℂ A)) :
    NormedSpace.GeometricStructureSpace ℂ A :=
  extremeKernel ⟨unitaryTranslate u phi, unitaryTranslate_mem_extremePoints_closedBall u
    (mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hphi)⟩

@[simp]
theorem coe_pureStateTranslateKernel (phi : StrongDual ℂ A)
    (hphi : IsPureNonUnitalState A phi) (u : unitary (Unitization ℂ A)) :
    (pureStateTranslateKernel phi hphi u).val = ((unitaryTranslate u phi).ker : Set A) := rfl

/-- Every original GSS point has a pure-state translate representative. -/
theorem exists_pureStateTranslateKernel_eq (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ∃ (phi : StrongDual ℂ A) (hphi : IsPureNonUnitalState A phi)
      (u : unitary (Unitization ℂ A)), pureStateTranslateKernel phi hphi u = I := by
  let J : Set A := I.val
  have hI : J ∈ NormedSpace.geometricStructureFamily ℂ A := I.property
  rw [geometricStructureFamily_eq_setOf_exists_pureState_unitaryTranslate] at hI
  obtain ⟨phi, hphi, u, hker⟩ := hI
  exact ⟨phi, hphi, u, Subtype.ext hker⟩

end MathlibAnnex.Analysis.CStarAlgebra
