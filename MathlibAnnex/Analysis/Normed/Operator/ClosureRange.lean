/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Corestriction to the norm closure of an operator range

The corestriction has dense range, not necessarily surjective range.
These declarations preserve the author's RCLike/normed-space assumptions;
no inner product, completeness, or inverse is required.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Topology

universe uF uH uK uI uJ

namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- The actual range corestriction into its norm closure, with the inherited norm. -/
def toClosureRange (T : H →L[𝕜] K) : H →L[𝕜] T.range.topologicalClosure :=
  T.codRestrict T.range.topologicalClosure (fun x =>
    T.range.le_topologicalClosure (T.mem_range_self x))

@[simp]
theorem toClosureRange_apply (T : H →L[𝕜] K) (x : H) :
    (T.toClosureRange x : K) = T x := rfl

/-- Corestriction to the norm-closed range has dense range, not necessarily
surjective range. This statement does not require completeness. -/
theorem denseRange_toClosureRange (T : H →L[𝕜] K) : DenseRange T.toClosureRange := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hy : (y : K) ∈ closure (Set.range T) := y.property
  obtain ⟨z, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp hy ε hε
  exact ⟨T.toClosureRange x, Set.mem_range_self x, hx⟩

end ContinuousLinearMap
