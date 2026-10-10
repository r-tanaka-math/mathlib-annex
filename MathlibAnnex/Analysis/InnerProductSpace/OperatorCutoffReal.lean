/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.OperatorPositivePartReal
import MathlibAnnex.Analysis.InnerProductSpace.OperatorCutoff

/-!
# Unconditional two-threshold cutoff over real Hilbert spaces

The parts are constructed in OperatorPositivePartReal, then the already supplied
RCLike analytic estimates and closed-literal-image theorem are applied. No real CFC
instance, Borel calculus or strict same-threshold assertion is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace ContinuousLinearMap
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Positive real cutoff part of the shifted Gram operator. -/
def realCutoffPositivePart (T : H →L[ℝ] K) (δ : ℝ) : H →L[ℝ] H :=
  realPositivePart (T.adjoint.comp T - (δ ^ 2) • .id ℝ H)

/-- The closed support space of the positive real cutoff part. -/
def realCutoffSubmodule (T : H →L[ℝ] K) (δ : ℝ) : Submodule ℝ H :=
  (realCutoffPositivePart T δ).range.topologicalClosure

/-- Actual decomposition, supplied without a real functional-calculus assumption. -/
theorem realCutoffPositivePart_decomposition (T : H →L[ℝ] K) (δ : ℝ) :
    let D := T.adjoint.comp T - (δ ^ 2) • .id ℝ H
    (realCutoffPositivePart T δ).IsPositive ∧ (realNegativePart D).IsPositive ∧
      D = realCutoffPositivePart T δ - realNegativePart D ∧
      (realNegativePart D).comp (realCutoffPositivePart T δ) = 0 := by
  dsimp only
  apply realPositivePart_decomposition
  have hc : IsSelfAdjoint ((δ ^ 2) • (ContinuousLinearMap.id ℝ H)) := by
    simp [IsSelfAdjoint, star_smul, star_eq_adjoint, adjoint_id]
  exact ((isPositive_adjoint_comp_self T).isSelfAdjoint.sub hc).isSymmetric

theorem isClosed_realCutoffSubmodule (T : H →L[ℝ] K) (δ : ℝ) :
    IsClosed (realCutoffSubmodule T δ : Set H) :=
  (realCutoffPositivePart T δ).range.isClosed_topologicalClosure

theorem orthogonal_realCutoffSubmodule (T : H →L[ℝ] K) (δ : ℝ) :
    (realCutoffSubmodule T δ)ᗮ = (realCutoffPositivePart T δ).ker :=
  orthogonal_closure_range_eq_ker_of_isPositive _
    (realCutoffPositivePart_decomposition T δ).1

/-- Quantified vector bounds also apply to the zero subspace. -/
theorem realCutoffSubmodule_bounds (T : H →L[ℝ] K) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ realCutoffSubmodule T δ, δ * ‖x‖ ≤ ‖T x‖) ∧
      (∀ x ∈ (realCutoffSubmodule T δ)ᗮ, ‖T x‖ ≤ δ * ‖x‖) := by
  obtain ⟨hR, hN, hdec, hNR⟩ := realCutoffPositivePart_decomposition T δ
  exact ⟨cutoff_lower_bound_of_positive_decomposition T hδ _ _ hR hdec hNR,
    cutoff_upper_bound_of_positive_decomposition T hδ _ _ hR hN hdec⟩

theorem isClosed_image_realCutoffSubmodule (T : H →L[ℝ] K) {δ : ℝ} (hδ : 0 < δ) :
    IsClosed (T '' (realCutoffSubmodule T δ : Set H)) :=
  isClosed_image_submodule_of_lower_bound T _ (isClosed_realCutoffSubmodule T δ)
    hδ (realCutoffSubmodule_bounds T hδ.le).1

/-- The real theorem: lower epsilon/2, upper epsilon/2, strict epsilon restriction
norm, and closed literal image. Zero and nonseparable Hilbert spaces are retained. -/
theorem exists_closed_submodule_two_threshold_cutoff_real
    (T : H →L[ℝ] K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Submodule ℝ H, IsClosed (S : Set H) ∧
      (∀ x ∈ S, (ε / 2) * ‖x‖ ≤ ‖T x‖) ∧
      (∀ x ∈ Sᗮ, ‖T x‖ ≤ (ε / 2) * ‖x‖) ∧
      ‖T.comp (Sᗮ).subtypeL‖ < ε ∧ IsClosed (T '' (S : Set H)) := by
  let S := realCutoffSubmodule T (ε / 2)
  have hd : 0 < ε / 2 := half_pos hε
  obtain ⟨hl, hu⟩ := realCutoffSubmodule_bounds T hd.le
  refine ⟨S, isClosed_realCutoffSubmodule T _, hl, hu, ?_,
    isClosed_image_realCutoffSubmodule T hd⟩
  have hb : ‖T.comp (Sᗮ).subtypeL‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ hd.le
    intro x
    exact hu x x.property
  exact hb.trans_lt (half_lt_self hε)

end ContinuousLinearMap
