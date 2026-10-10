/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarSupport
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# Krein-Milman for weak-star support families

The weak-star support family is the weak-star closed convex hull of its
extreme points. When the primal set lies in the unit ball, those extreme
points are exactly its intersection with the extreme points of the dual
ball. The canonical dual identification preserves extreme points because
extremality is algebraic; no norm-topological compactness is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Extreme points are unchanged by the canonical dual identification.
The topologies differ, but the real affine operations and the ball carrier
agree definitionally. -/
theorem mem_extremePoints_closedBall_toStrongDual_iff (f : WeakDual 𝕜 E) :
    f.toStrongDual ∈ (closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ ↔
      f ∈ (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ :=
  Iff.rfl

/-- Extreme points of a support face are extreme points of the whole dual
ball; the reverse inclusion holds after intersecting with the support face. -/
theorem extremePoints_weakStarSupportFunctionals_eq_inter {F : Set E}
    (hF : F ⊆ closedBall (0 : E) 1) :
    (weakStarSupportFunctionals 𝕜 F).extremePoints ℝ =
      weakStarSupportFunctionals 𝕜 F ∩
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ :=
  (isExtreme_weakStarSupportFunctionals 𝕜 hF).extremePoints_eq

/-- Krein-Milman, with closure taken in WeakDual, including the empty case. -/
theorem closure_convexHull_extremePoints_weakStarSupportFunctionals (F : Set E) :
    closure (convexHull ℝ ((weakStarSupportFunctionals 𝕜 F).extremePoints ℝ)) =
      weakStarSupportFunctionals 𝕜 F := by
  letI : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  exact closure_convexHull_extremePoints (isCompact_weakStarSupportFunctionals 𝕜 F)
    (convex_weakStarSupportFunctionals 𝕜 F)

/-- The exact weak-star closed-convex-hull formula used by the maximal-face
argument: extreme points are taken in the full dual unit ball. -/
theorem closure_convexHull_inter_extremePoints_closedBall_weakStarSupportFunctionals
    {F : Set E} (hF : F ⊆ closedBall (0 : E) 1) :
    closure (convexHull ℝ (weakStarSupportFunctionals 𝕜 F ∩
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ)) =
      weakStarSupportFunctionals 𝕜 F := by
  rw [← extremePoints_weakStarSupportFunctionals_eq_inter 𝕜 hF]
  exact closure_convexHull_extremePoints_weakStarSupportFunctionals 𝕜 F

/-- Every nonempty support family contains an extreme point, by weak-star
compactness. This statement does not itself claim extremality in the whole ball. -/
theorem nonempty_extremePoints_weakStarSupportFunctionals {F : Set E}
    (hne : (supportFunctionals 𝕜 F).Nonempty) :
    ((weakStarSupportFunctionals 𝕜 F).extremePoints ℝ).Nonempty := by
  letI : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  exact (isCompact_weakStarSupportFunctionals 𝕜 F).extremePoints_nonempty
    ((nonempty_weakStarSupportFunctionals_iff 𝕜 F).2 hne)

/-- A nonempty support family of a primal ball subset contains a functional
which is extreme in the entire dual unit ball. -/
theorem exists_mem_supportFunctionals_extremePoints_closedBall {F : Set E}
    (hne : (supportFunctionals 𝕜 F).Nonempty) (hF : F ⊆ closedBall (0 : E) 1) :
    ∃ f : StrongDual 𝕜 E, f ∈ supportFunctionals 𝕜 F ∧
      f ∈ (closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ := by
  obtain ⟨f, hf⟩ := nonempty_extremePoints_weakStarSupportFunctionals 𝕜 hne
  rw [extremePoints_weakStarSupportFunctionals_eq_inter 𝕜 hF] at hf
  exact ⟨f.toStrongDual, hf.1, (mem_extremePoints_closedBall_toStrongDual_iff 𝕜 f).2 hf.2⟩

end NormedSpace
