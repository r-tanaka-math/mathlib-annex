/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Maximal proper real convex faces of the closed unit ball

`IsExtreme` is the existing Mathlib extreme-subset predicate. Convexity is a
separate requirement. Maximality is among proper convex faces. In particular,
exposedness, supporting-functional existence, compactness, and extreme supporting
functionals are not fields of the predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace NormedSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty proper real convex face, maximal among the proper real convex faces
of the closed unit ball. -/
structure IsMaximalFace (F : Set E) : Prop where
  nonempty : F.Nonempty
  convex : Convex ℝ F
  isExtreme : IsExtreme ℝ (Metric.closedBall (0 : E) 1) F
  ne_closedBall : F ≠ Metric.closedBall (0 : E) 1
  maximal : ∀ G : Set E, F ⊆ G → Convex ℝ G →
    IsExtreme ℝ (Metric.closedBall (0 : E) 1) G →
    G ≠ Metric.closedBall (0 : E) 1 → G = F

theorem IsMaximalFace.subset_closedBall {F : Set E} (hF : IsMaximalFace F) :
    F ⊆ Metric.closedBall (0 : E) 1 := hF.isExtreme.subset

/-- The zero space has no nonempty proper maximal face. -/
theorem not_isMaximalFace_of_subsingleton [Subsingleton E] (F : Set E) :
    ¬ IsMaximalFace F := by
  intro hF
  apply hF.ne_closedBall
  apply Set.Subset.antisymm hF.subset_closedBall
  obtain ⟨x, hx⟩ := hF.nonempty
  intro y _
  exact (Subsingleton.elim x y) ▸ hx

end NormedSpace
