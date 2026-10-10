/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeDecomposition
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.MatrixCoefficientSeparation

/-!
# Noninclusion of distinct extreme dual support slices

Apply the actual original-algebra cyclic coefficient realizations to two
arbitrary extreme dual functionals. The previously proved irreducibility
criterion applies to these constructed representations. The two-representation
separation theorem then gives a witness in the original algebra.

This proves Notes 11.13 with the weaker and correct requirement that the
second value is not one. A pure phase change can have modulus one. The
rank-one equality argument replaces the separate independent/dependent-vector
calculation, while keeping nonzero representations, unit vectors and the
nonunital positive exact interpolation steps explicit.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- Any two distinct extreme points of the complex dual unit ball can be
separated by a contractive original-algebra element at value one. -/
theorem exists_norm_le_one_apply_eq_one_apply_ne_one_of_mem_extremePoints_dual_closedBall
    {rho tau : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (htau : tau ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hne : rho ≠ tau) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ rho a = 1 ∧ tau a ≠ 1 := by
  have hA : ¬ Subsingleton A := by
    intro hsub
    letI : Subsingleton A := hsub
    apply hne
    apply ContinuousLinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have hnr := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  have hnt := norm_eq_one_of_mem_extremePoints_dual_closedBall htau
  have hr0 : rho ≠ 0 := norm_ne_zero_iff.mp (by rw [hnr]; exact one_ne_zero)
  have ht0 : tau ≠ 0 := norm_ne_zero_iff.mp (by rw [hnt]; exact one_ne_zero)
  let K : Bool → Type _ := fun i => match i with
    | false => NonUnitalFunctional.CyclicSpace rho hr0
    | true => NonUnitalFunctional.CyclicSpace tau ht0
  letI (i : Bool) : NormedAddCommGroup (K i) := match i with
    | false => inferInstance
    | true => inferInstance
  letI (i : Bool) : InnerProductSpace ℂ (K i) := match i with
    | false => inferInstance
    | true => inferInstance
  letI (i : Bool) : CompleteSpace (K i) := match i with
    | false => inferInstance
    | true => inferInstance
  let pi : ∀ i, NonUnitalCStarRepresentation A (K i) := fun i => match i with
    | false => NonUnitalFunctional.cyclicRepresentation rho hr0
    | true => NonUnitalFunctional.cyclicRepresentation tau ht0
  let x : ∀ i, K i := fun i => match i with
    | false => NonUnitalFunctional.cyclicSourceVector rho hr0
    | true => NonUnitalFunctional.cyclicSourceVector tau ht0
  let y : ∀ i, K i := fun i => match i with
    | false => NonUnitalFunctional.cyclicTargetVector rho hr0
    | true => NonUnitalFunctional.cyclicTargetVector tau ht0
  have hirr : ∀ i, (pi i).IsIrreducible := by
    intro i
    cases i
    · exact NonUnitalFunctional.isIrreducible_cyclicRepresentation rho hr0 hrho
    · exact NonUnitalFunctional.isIrreducible_cyclicRepresentation tau ht0 htau
  have hx : ∀ i, ‖x i‖ = 1 := by
    intro i
    cases i
    · exact NonUnitalFunctional.norm_cyclicSourceVector rho hr0
    · exact NonUnitalFunctional.norm_cyclicSourceVector tau ht0
  have hy : ∀ i, ‖y i‖ = 1 := by
    intro i
    cases i
    · exact NonUnitalFunctional.norm_cyclicTargetVector rho hr0
    · exact NonUnitalFunctional.norm_cyclicTargetVector tau ht0
  have hcr : NonUnitalCStarRepresentation.matrixCoefficient (pi false) (x false) (y false) =
      rho := NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one
        rho hr0 hnr
  have hct : NonUnitalCStarRepresentation.matrixCoefficient (pi true) (x true) (y true) =
      tau := NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one
        tau ht0 hnt
  have hcne : NonUnitalCStarRepresentation.matrixCoefficient (pi false) (x false) (y false) ≠
      NonUnitalCStarRepresentation.matrixCoefficient (pi true) (x true) (y true) := by
    rwa [hcr, hct]
  obtain ⟨a, han, ha, hta⟩ :=
    NonUnitalCStarRepresentation.exists_norm_le_one_matrixCoefficient_eq_one_ne_one
      pi hirr x y hx hy hcne
  exact ⟨a, han, by simpa only [hcr] using ha, by simpa only [hct] using hta⟩

/-- Notes 11.13 in the already shared support-slice definition. -/
theorem not_unitBallSupportFace_subset_of_ne_of_mem_extremePoints_dual_closedBall
    {rho tau : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (htau : tau ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hne : rho ≠ tau) :
    ¬ NormedSpace.unitBallSupportFace ℂ rho ⊆ NormedSpace.unitBallSupportFace ℂ tau := by
  obtain ⟨a, han, ha, hta⟩ :=
    exists_norm_le_one_apply_eq_one_apply_ne_one_of_mem_extremePoints_dual_closedBall
      hrho htau hne
  intro hsubset
  exact hta (hsubset ⟨mem_closedBall_zero_iff.mpr han, ha⟩).2

/-- Inclusion of two extreme support slices forces equality of the functionals,
not only equality of kernels or representation classes. -/
theorem eq_of_unitBallSupportFace_subset_of_mem_extremePoints_dual_closedBall
    {rho tau : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (htau : tau ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hsubset : NormedSpace.unitBallSupportFace ℂ rho ⊆
      NormedSpace.unitBallSupportFace ℂ tau) : rho = tau := by
  by_contra hne
  exact not_unitBallSupportFace_subset_of_ne_of_mem_extremePoints_dual_closedBall
    hrho htau hne hsubset

end MathlibAnnex.Analysis.CStarAlgebra
