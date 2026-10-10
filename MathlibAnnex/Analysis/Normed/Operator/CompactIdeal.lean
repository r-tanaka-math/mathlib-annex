/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

/-!
# The compact-operator ideal on a normed space

These six declarations use no inner product, orthogonal projection or Hilbert basis.
The carrier is the existing IsCompactOperator predicate with the original operator norm.
Completeness is required only where the stated result needs it.
-/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded operator with finite-dimensional range is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)] : IsCompactOperator T := by
  let M : Submodule 𝕜 F := LinearMap.range T.toLinearMap
  letI : ProperSpace M := FiniteDimensional.proper_rclike 𝕜 M
  let T' : E →L[𝕜] M := T.codRestrict M (fun x => ⟨x, rfl⟩)
  have hT' : IsCompactOperator T' := isCompactOperator_of_locallyCompactSpace_dom T'
  exact hT'.clm_comp M.subtypeL

/-- The existing compact-operator predicate, bundled as a two-sided ideal. -/
def compactOperatorIdeal (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : TwoSidedIdeal (E →L[𝕜] E) :=
  TwoSidedIdeal.mk' {T | IsCompactOperator T}
    isCompactOperator_zero
    (fun {T S} hT hS => hT.add hS)
    (fun {T} hT => hT.neg)
    (fun {T S} hS => hS.clm_comp T)
    (fun {T S} hT => hT.comp_clm S)

@[simp]
theorem mem_compactOperatorIdeal (T : E →L[𝕜] E) :
    T ∈ compactOperatorIdeal 𝕜 E ↔ IsCompactOperator T := by
  simp only [compactOperatorIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

/-- This is exactly the carrier of Mathlib's compact-operator submodule. -/
theorem coe_compactOperatorIdeal :
    (compactOperatorIdeal 𝕜 E : Set (E →L[𝕜] E)) =
      (compactOperator (RingHom.id 𝕜) E E : Set (E →L[𝕜] E)) := by
  ext T
  exact mem_compactOperatorIdeal T

/-- Closedness refers to the unchanged operator norm on the ambient ring. -/
theorem isClosed_compactOperatorIdeal [CompleteSpace E] :
    IsClosed (compactOperatorIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  simpa only [compactOperatorIdeal, TwoSidedIdeal.coe_mk'] using
    (isClosed_setOf_isCompactOperator :
      IsClosed {T : E →L[𝕜] E | IsCompactOperator T})

/-- In particular a finite-dimensional operator ring consists entirely of compacts. -/
theorem compactOperatorIdeal_eq_top_iff :
    compactOperatorIdeal 𝕜 E = ⊤ ↔ FiniteDimensional 𝕜 E := by
  constructor
  · intro h
    have hc : IsCompactOperator (ContinuousLinearMap.id 𝕜 E) :=
      (mem_compactOperatorIdeal _).1 (by rw [h]; exact TwoSidedIdeal.mem_top _)
    exact FiniteDimensional.of_isCompactOperator_id (𝕜 := 𝕜) hc
  · intro h
    letI := h
    apply top_unique
    intro T _
    exact (mem_compactOperatorIdeal T).2 T.isCompactOperator_of_finiteDimensional_range

end ContinuousLinearMap
