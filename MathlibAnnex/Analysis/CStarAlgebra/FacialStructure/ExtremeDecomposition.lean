/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FunctionalRealization
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PositiveTranslateUniqueness

/-!
# Pure-state and unitary decomposition of arbitrary extreme dual functionals

Start with an arbitrary extreme point of the dual unit ball of a nontrivial,
possibly nonunital C-star algebra. The actual Hahn--Banach/auxiliary-GNS model
is compressed to the original-algebra closed orbit. Its two unit vectors,
coefficient recovery and original-algebra cyclicity are proved in
`FunctionalRealization`; the existing extreme-coefficient criterion then
makes this actual representation irreducible. Unitary transitivity gives a
pure positive translate. The positive state is unique, not its translating
unitary. No extremality of the Hahn--Banach extension is used.

This closes the existence and state-uniqueness assertions of Notes 11.9.
It does not assert maximality of the support slice or a singleton of all
supporting functionals; those require the later slice-separation theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]

/-- The explicitly constructed original-algebra cyclic representation of an
arbitrary extreme dual functional is nonzero and irreducible. -/
theorem NonUnitalFunctional.isIrreducible_cyclicRepresentation
    (rho : StrongDual ℂ A) (hrho : rho ≠ 0)
    (hext : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NonUnitalFunctional.cyclicRepresentation rho hrho).IsIrreducible := by
  have hn := norm_eq_one_of_mem_extremePoints_dual_closedBall hext
  have hx := NonUnitalFunctional.norm_cyclicSourceVector rho hrho
  have hy := NonUnitalFunctional.norm_cyclicTargetVector rho hrho
  have hcoeff := NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one
    rho hrho hn
  apply NonUnitalCStarRepresentation.isIrreducible_of_extreme_matrixCoefficient_of_denseRange
    (NonUnitalFunctional.cyclicRepresentation rho hrho)
    (NonUnitalFunctional.cyclicSourceVector rho hrho)
    (NonUnitalFunctional.cyclicTargetVector rho hrho) hx hy
  · rwa [hcoeff]
  · rwa [hcoeff]
  · exact NonUnitalFunctional.denseRange_cyclicRepresentation rho hrho

variable [PartialOrder A] [StarOrderedRing A]

/-- Every extreme dual unit functional is a unitary translate of a genuine
pure nonunital state. Existence is proved from the arbitrary extreme point,
not from a pre-existing positive translate or irreducible realization. -/
theorem exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃ phi : StrongDual ℂ A, IsPureNonUnitalState A phi ∧
      ∃ u : unitary (Unitization ℂ A),
        unitaryTranslate u rho = phi ∧ rho = unitaryTranslate (star u) phi := by
  have hn := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  have hne : rho ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  have hpi := NonUnitalFunctional.isIrreducible_cyclicRepresentation rho hne hrho
  have hx := NonUnitalFunctional.norm_cyclicSourceVector rho hne
  have hy := NonUnitalFunctional.norm_cyclicTargetVector rho hne
  have hcoeff := NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one
    rho hne hn
  obtain ⟨u, hu, hpure, hrecover⟩ :=
    NonUnitalCStarRepresentation.exists_unitaryTranslate_eq_pureState_of_isIrreducible
      (NonUnitalFunctional.cyclicRepresentation rho hne) hpi
      (NonUnitalFunctional.cyclicSourceVector rho hne)
      (NonUnitalFunctional.cyclicTargetVector rho hne) hx hy
  refine ⟨_, hpure, u, ?_, ?_⟩
  · simpa only [hcoeff] using hu
  · simpa only [hcoeff] using hrecover

/-- The positive pure state in the unitary decomposition is unique.
The unitary is existentially quantified inside the unique-state property. -/
theorem existsUnique_pureState_unitaryTranslate
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃! phi : StrongDual ℂ A, IsPureNonUnitalState A phi ∧
      ∃ u : unitary (Unitization ℂ A),
        unitaryTranslate u rho = phi ∧ rho = unitaryTranslate (star u) phi := by
  obtain ⟨phi, hphi, u, hu, hrecover⟩ :=
    exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall hrho
  refine ⟨phi, ⟨hphi, u, hu, hrecover⟩, ?_⟩
  rintro psi ⟨hpsi, v, hv, _⟩
  have hu0 : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate u rho a := by
    intro a ha
    rw [hu]
    exact hphi.1.1 a ha
  have hv0 : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate v rho a := by
    intro a ha
    rw [hv]
    exact hpsi.1.1 a ha
  calc
    psi = unitaryTranslate v rho := hv.symm
    _ = unitaryTranslate u rho :=
      unitaryTranslate_eq_of_nonneg_of_mem_extremePoints_dual_closedBall hrho v u hv0 hu0
    _ = phi := hu

/-- Every extreme dual unit functional attains the value one at a norm-one
member of the original algebra, not merely of its unitization. -/
theorem exists_norm_eq_one_apply_eq_one_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃ a : A, ‖a‖ = 1 ∧ rho a = 1 := by
  obtain ⟨phi, hphi, u, hu, _⟩ :=
    exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall hrho
  apply exists_norm_eq_one_apply_eq_one_of_nonneg_unitaryTranslate u hrho
  intro a ha
  rw [hu]
  exact hphi.1.1 a ha

/-- The shared value-one slice of an arbitrary extreme dual functional is
nonempty. No maximality or support-uniqueness claim is part of this theorem. -/
theorem nonempty_unitBallSupportFace_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NormedSpace.unitBallSupportFace ℂ rho).Nonempty := by
  obtain ⟨a, ha, hval⟩ := exists_norm_eq_one_apply_eq_one_of_mem_extremePoints_dual_closedBall hrho
  exact ⟨a, mem_closedBall_zero_iff.mpr ha.le, hval⟩

end MathlibAnnex.Analysis.CStarAlgebra
