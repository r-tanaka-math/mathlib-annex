/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFace
public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarKreinMilman

/-!
# Extreme supporting functionals of maximal faces

Common support establishes nonemptiness, weak-star compactness supplies an
extreme point, and faciality promotes it to an extreme point of the full dual
ball. Maximality identifies the primal face with its supporting slice. None
of these arguments gives uniqueness in a general normed space.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- A nonempty convex sphere subset has a common supporting functional
which is extreme in the entire dual unit ball. -/
theorem exists_extreme_dual_eq_one_of_convex_subset_sphere {C : Set E}
    (hne : C.Nonempty) (hconv : Convex ℝ C) (hC : C ⊆ sphere (0 : E) 1) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧
      f ∈ (closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ ∧
      ∀ x ∈ C, f x = 1 := by
  have hball : C ⊆ closedBall (0 : E) 1 := by
    intro x hx
    have hn : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hC hx
    exact mem_closedBall_zero_iff.2 hn.le
  obtain ⟨f, hf, hext⟩ := exists_mem_supportFunctionals_extremePoints_closedBall 𝕜
    (nonempty_supportFunctionals_of_convex_subset_sphere 𝕜 hne hconv hC) hball
  exact ⟨f, norm_eq_one_of_mem_supportFunctionals 𝕜 hne
    (fun x hx => mem_closedBall_zero_iff.1 (hball hx)) hf, hext, hf.2⟩

theorem IsMaximalFace.nonempty_weakStarSupportFunctionals {F : Set E}
    (hF : IsMaximalFace F) : (weakStarSupportFunctionals 𝕜 F).Nonempty :=
  (nonempty_weakStarSupportFunctionals_iff 𝕜 F).2 (hF.nonempty_supportFunctionals 𝕜)

/-- A maximal proper face has an extreme supporting functional. This is an
existence theorem, not the C-star-algebra uniqueness theorem. -/
theorem IsMaximalFace.exists_extreme_support {F : Set E} (hF : IsMaximalFace F) :
    ∃ f : StrongDual 𝕜 E, f ∈ supportFunctionals 𝕜 F ∧
      f ∈ (closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ :=
  exists_mem_supportFunctionals_extremePoints_closedBall 𝕜
    (hF.nonempty_supportFunctionals 𝕜) hF.subset_closedBall

/-- Every maximal proper face is the slice of an extreme dual unit functional.
The converse and uniqueness require further structure and are not asserted. -/
theorem IsMaximalFace.exists_extreme_eq_unitBallSupportFace {F : Set E}
    (hF : IsMaximalFace F) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧
      f ∈ (closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ ∧
      F = unitBallSupportFace 𝕜 f := by
  obtain ⟨f, hf, hext⟩ := hF.exists_extreme_support 𝕜
  exact ⟨f, norm_eq_one_of_mem_supportFunctionals 𝕜 hF.nonempty
    (fun x hx => mem_closedBall_zero_iff.1 (hF.subset_closedBall hx)) hf,
    hext, hF.eq_unitBallSupportFace 𝕜 hf⟩

end NormedSpace
