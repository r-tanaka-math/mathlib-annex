/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeSliceSeparation
import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarMaximalFace

/-!
# Maximal faces and their entire supporting families

For a nontrivial possibly nonunital C-star algebra, the maximal proper faces
of the closed unit ball are exactly the value-one slices of extreme dual
unit functionals. Every such slice has exactly one supporting functional in
the entire closed dual ball.

The latter conclusion is not obtained by renaming uniqueness among extreme
points. We identify the intersection of the actual weak-star support family
with the extreme dual ball and apply the received weak-star Krein--Milman
identity. The resulting singleton is then carried back to the original
`supportFunctionals`. All face and support definitions are imported from MAIN.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

/-- The converse half of Notes 11.14: the slice of an arbitrary extreme
functional is a maximal proper face, not merely a nonempty exposed face. -/
theorem isMaximalFace_unitBallSupportFace_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.IsMaximalFace (NormedSpace.unitBallSupportFace ℂ rho) := by
  have hn := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  obtain ⟨G, hFG, hG⟩ := NormedSpace.exists_isMaximalFace_of_convex_subset_sphere
    (nonempty_unitBallSupportFace_of_mem_extremePoints_dual_closedBall hrho)
    (NormedSpace.convex_unitBallSupportFace ℂ rho)
    (NormedSpace.unitBallSupportFace_subset_sphere ℂ hn.le)
  obtain ⟨tau, _, htau, hGtau⟩ := hG.exists_extreme_eq_unitBallSupportFace ℂ
  have heq : rho = tau :=
    eq_of_unitBallSupportFace_subset_of_mem_extremePoints_dual_closedBall hrho htau
      (by simpa only [hGtau] using hFG)
  rw [heq]
  rwa [hGtau] at hG

/-- The actual weak-star support family of an extreme slice has one point.
The closure and convex hull here are explicitly in WeakDual, not StrongDual. -/
theorem weakStarSupportFunctionals_unitBallSupportFace_eq_singleton
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.weakStarSupportFunctionals ℂ (NormedSpace.unitBallSupportFace ℂ rho) =
      {rho.toWeakDual} := by
  let F : Set A := NormedSpace.unitBallSupportFace ℂ rho
  have hn := norm_eq_one_of_mem_extremePoints_dual_closedBall hrho
  have hball : F ⊆ closedBall (0 : A) 1 := fun _ hx => hx.1
  have hrs : rho ∈ NormedSpace.supportFunctionals ℂ F :=
    ⟨hn.le, fun _ hx => hx.2⟩
  have hinter : NormedSpace.weakStarSupportFunctionals ℂ F ∩
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ =
        {rho.toWeakDual} := by
    ext f
    constructor
    · rintro ⟨hf, hext⟩
      have hext' := (NormedSpace.mem_extremePoints_closedBall_toStrongDual_iff ℂ f).mpr hext
      have heq : rho = f.toStrongDual :=
        eq_of_unitBallSupportFace_subset_of_mem_extremePoints_dual_closedBall hrho hext'
          (fun a ha => ⟨ha.1, hf.2 a ha⟩)
      apply Set.mem_singleton_iff.mpr
      exact (congrArg (fun g : StrongDual ℂ A => g.toWeakDual) heq).symm
    · intro hf
      have hfr : f = StrongDual.toWeakDual rho := Set.mem_singleton_iff.mp hf
      rw [hfr]
      exact ⟨hrs, (NormedSpace.mem_extremePoints_closedBall_toStrongDual_iff
        ℂ (StrongDual.toWeakDual rho)).mp hrho⟩
  have hkm := NormedSpace.closure_convexHull_inter_extremePoints_closedBall_weakStarSupportFunctionals
    ℂ hball
  rw [hinter, convexHull_singleton, closure_singleton] at hkm
  exact hkm.symm

/-- The full supporting family, including nonextreme functionals, is a
singleton. This is the complete uniqueness assertion in Notes 11.14. -/
theorem supportFunctionals_unitBallSupportFace_eq_singleton
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.supportFunctionals ℂ (NormedSpace.unitBallSupportFace ℂ rho) = {rho} := by
  rw [← NormedSpace.image_toStrongDual_weakStarSupportFunctionals,
    weakStarSupportFunctionals_unitBallSupportFace_eq_singleton hrho,
    Set.image_singleton]
  rfl

/-- The maximal proper faces of the original algebra's unit ball are exactly
its extreme dual value-one slices. -/
theorem isMaximalFace_iff_exists_mem_extremePoints_dual_closedBall (F : Set A) :
    NormedSpace.IsMaximalFace F ↔ ∃ rho : StrongDual ℂ A,
      rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∧
        F = NormedSpace.unitBallSupportFace ℂ rho := by
  constructor
  · intro hF
    obtain ⟨rho, _, hrho, hFrho⟩ := hF.exists_extreme_eq_unitBallSupportFace ℂ
    exact ⟨rho, hrho, hFrho⟩
  · rintro ⟨rho, hrho, rfl⟩
    exact isMaximalFace_unitBallSupportFace_of_mem_extremePoints_dual_closedBall hrho

/-- A maximal proper face has exactly one extreme value-one representation,
and its entire supporting family consists of that same functional. -/
theorem existsUnique_extreme_support_of_isMaximalFace {F : Set A}
    (hF : NormedSpace.IsMaximalFace F) :
    ∃! rho : StrongDual ℂ A,
      rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∧
        F = NormedSpace.unitBallSupportFace ℂ rho ∧
          NormedSpace.supportFunctionals ℂ F = {rho} := by
  obtain ⟨rho, hrho, hFrho⟩ :=
    (isMaximalFace_iff_exists_mem_extremePoints_dual_closedBall F).mp hF
  have hs : NormedSpace.supportFunctionals ℂ F = {rho} := by
    rw [hFrho]
    exact supportFunctionals_unitBallSupportFace_eq_singleton hrho
  refine ⟨rho, ⟨hrho, hFrho, hs⟩, ?_⟩
  rintro tau ⟨_, _, hst⟩
  have hmem : tau ∈ ({rho} : Set (StrongDual ℂ A)) := by
    rw [← hs, hst]
    exact Set.mem_singleton tau
  exact Set.mem_singleton_iff.mp hmem

end MathlibAnnex.Analysis.CStarAlgebra
