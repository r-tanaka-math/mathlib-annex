import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Linarith

/-!
# Seminorms quantitatively equivalent to a reference norm

The reference norm stays on the carrier. The eight fields store a real seminorm,
two positive comparison constants, both inequalities, and continuity.
-/

namespace MathlibAnnex

/-- A continuous seminorm with explicit positive lower and upper norm comparisons. -/
structure EquivalentSeminorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  p : Seminorm ℝ E
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_le : ∀ x, lower * ‖x‖ ≤ p x
  le_upper : ∀ x, p x ≤ upper * ‖x‖
  continuous_p : Continuous p

namespace EquivalentSeminorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (M : EquivalentSeminorm E)

/-- The closed unit ball of the stored seminorm, on the reference carrier. -/
def closedUnitBall : Set E := M.p.closedBall 0 1

/-- The unit sphere of the stored seminorm, on the reference carrier. -/
def unitSphere : Set E := {x | M.p x = 1}

@[simp] theorem mem_closedUnitBall {x : E} : x ∈ M.closedUnitBall ↔ M.p x ≤ 1 := by
  simp [closedUnitBall]

@[simp] theorem mem_unitSphere {x : E} : x ∈ M.unitSphere ↔ M.p x = 1 := Iff.rfl

@[simp] theorem zero_mem_closedUnitBall : (0 : E) ∈ M.closedUnitBall := by
  simp [closedUnitBall]

theorem closedUnitBall_nonempty : M.closedUnitBall.Nonempty :=
  ⟨0, M.zero_mem_closedUnitBall⟩

/-- The positive lower comparison makes the seminorm definite. -/
theorem eq_zero_of_apply_eq_zero {x : E} (hx : M.p x = 0) : x = 0 := by
  have h : M.lower * ‖x‖ ≤ 0 := by simpa [hx] using M.lower_le x
  have hnorm : ‖x‖ = 0 := by
    have hn : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith [M.lower_pos]
  exact norm_eq_zero.mp hnorm

/-- A continuous linear map bounded pointwise by the model seminorm. -/
def IsContraction (A : E →L[ℝ] F) : Prop := ∀ x, ‖A x‖ ≤ M.p x

@[simp] theorem isContraction_zero : M.IsContraction (0 : E →L[ℝ] F) := by
  intro x
  simp

/-- The set of all continuous linear contractions for the model seminorm. -/
def contractionSet (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Set (E →L[ℝ] F) := {A | M.IsContraction A}

@[simp] theorem mem_contractionSet {A : E →L[ℝ] F} :
    A ∈ M.contractionSet F ↔ M.IsContraction A := Iff.rfl

end EquivalentSeminorm
end MathlibAnnex
