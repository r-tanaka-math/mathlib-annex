/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic

/-!
# A valid two-threshold cutoff for a bounded Hilbert-space operator

The analytic reduction from a positive/negative decomposition is RCLike-general.
The unconditional CFC construction in this file is complex. The pinned library
supplies the real selfadjoint CFC on complex Hilbert operators, but does not supply
it on real Hilbert operators. The general-real existence step remains explicitly
unresolved; no CFC instance is postulated here for real Hilbert operators.

For delta > 0 the complex construction gives lower >= delta on a closed subspace
and upper <= delta on its orthogonal complement. With delta = epsilon / 2 the latter
operator norm is < epsilon. It does not assert lower >= epsilon with upper < epsilon.
All inequalities are quantified over vectors, also when the chosen subspace is zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set InnerProductSpace RCLike
open scoped ComplexConjugate NNReal

namespace ContinuousLinearMap

section Analytic

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [completeH : CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [completeK : CompleteSpace K]

include completeH in
/-- The support subspace of a positive bounded operator has its kernel as orthogonal
complement. This is a norm closure of a range, not a claim that the range is closed. -/
theorem orthogonal_closure_range_eq_ker_of_isPositive
    (R : H →L[𝕜] H) (hR : R.IsPositive) :
    R.range.topologicalClosureᗮ = R.ker := by
  letI : CompleteSpace R.ker := R.isClosed_ker.completeSpace_coe
  have hsupport : R.range.topologicalClosure = R.kerᗮ := by
    simpa only [hR.isSymmetric.clm_adjoint_eq] using R.orthogonal_ker.symm
  rw [hsupport, R.ker.orthogonal_orthogonal]

/-- Positive and negative orthogonal parts give a lower bound on the norm-closed
range of the positive part. The decomposition assumptions are algebraic identities;
for complex operators they are actually constructed below by the real-valued CFC. -/
theorem cutoff_lower_bound_of_positive_decomposition
    (T : H →L[𝕜] K) {δ : ℝ} (hδ : 0 ≤ δ)
    (R N : H →L[𝕜] H) (hR : R.IsPositive)
    (hdec : T.adjoint.comp T - ((δ ^ 2 : ℝ) : 𝕜) • .id 𝕜 H = R - N)
    (hNR : N.comp R = 0) :
    ∀ x ∈ R.range.topologicalClosure, δ * ‖x‖ ≤ ‖T x‖ := by
  have hrange : ∀ x ∈ R.range, δ * ‖x‖ ≤ ‖T x‖ := by
    rintro _ ⟨y, rfl⟩
    have hzero : N (R y) = 0 := congrArg (fun A : H →L[𝕜] H => A y) hNR
    have he := congrArg (fun A : H →L[𝕜] H =>
      RCLike.re (inner 𝕜 (R y) (A (R y)))) hdec
    simp only [sub_apply, comp_apply, smul_apply, id_apply, inner_sub_right,
      inner_smul_right, map_sub, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq, hzero, inner_zero_right, map_zero, sub_zero] at he
    have hq := T.apply_norm_sq_eq_inner_adjoint_right (R y)
    have hp := hR.re_inner_nonneg_right (R y)
    have hsquare : (δ * ‖R y‖) ^ 2 ≤ ‖T (R y)‖ ^ 2 := by
      change ‖T (R y)‖ ^ 2 = RCLike.re (inner 𝕜 (R y)
        (T.adjoint (T (R y)))) at hq
      nlinarith
    change δ * ‖R y‖ ≤ ‖T (R y)‖
    nlinarith [norm_nonneg (T (R y)), mul_nonneg hδ (norm_nonneg (R y))]
  intro x hx
  change x ∈ closure (R.range : Set H) at hx
  exact closure_minimal hrange
    (isClosed_le (continuous_const.mul continuous_norm) T.continuous.norm) hx

/-- The complementary upper bound uses the negative part and the exact kernel
identity; it does not invoke a supremum or infimum on an empty unit sphere. -/
theorem cutoff_upper_bound_of_positive_decomposition
    (T : H →L[𝕜] K) {δ : ℝ} (hδ : 0 ≤ δ)
    (R N : H →L[𝕜] H) (hR : R.IsPositive) (hN : N.IsPositive)
    (hdec : T.adjoint.comp T - ((δ ^ 2 : ℝ) : 𝕜) • .id 𝕜 H = R - N) :
    ∀ x ∈ R.range.topologicalClosureᗮ, ‖T x‖ ≤ δ * ‖x‖ := by
  intro x hx
  have hRx : R x = 0 := by
    rw [orthogonal_closure_range_eq_ker_of_isPositive R hR] at hx
    exact hx
  have he := congrArg (fun A : H →L[𝕜] H =>
    RCLike.re (inner 𝕜 x (A x))) hdec
  simp only [sub_apply, comp_apply, smul_apply, id_apply, inner_sub_right,
    inner_smul_right, map_sub, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq, hRx, inner_zero_right, map_zero, zero_sub, inner_neg_right, map_neg] at he
  have hq := T.apply_norm_sq_eq_inner_adjoint_right x
  change ‖T x‖ ^ 2 = RCLike.re (inner 𝕜 x (T.adjoint (T x))) at hq
  have hp := hN.re_inner_nonneg_right x
  have hsquare : ‖T x‖ ^ 2 ≤ (δ * ‖x‖) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (T x), mul_nonneg hδ (norm_nonneg x)]

include completeH in
/-- A bounded-below restriction to a norm-closed subspace has closed literal image.
The closed range is proved via an antilipschitz map on the complete subtype. -/
theorem isClosed_image_submodule_of_lower_bound
    (T : H →L[𝕜] K) (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖) :
    IsClosed (T '' (S : Set H)) := by
  letI : CompleteSpace S := hS.completeSpace_coe
  let F : S →L[𝕜] K := T.comp S.subtypeL
  have ha : AntilipschitzWith (⟨δ⁻¹, (inv_pos.mpr hδ).le⟩ : ℝ≥0) F := by
    apply F.antilipschitz_of_bound
    intro x
    change ‖(x : H)‖ ≤ δ⁻¹ * ‖T (x : H)‖
    rw [inv_mul_eq_div, le_div_iff₀ hδ]
    simpa only [mul_comm] using hlower x x.property
  have heq : Set.range F = T '' (S : Set H) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← heq]
  exact ha.isClosed_range F.uniformContinuous

end Analytic

section Complex

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The positive part of the shifted Gram operator, in B(H) itself. -/
def cutoffPositivePart (T : H →L[ℂ] K) (δ : ℝ) : H →L[ℂ] H :=
  (T.adjoint.comp T - ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H)⁺

/-- The requested norm-closed subspace, with no claim that its projection belongs
to any nonunital research algebra. -/
def cutoffSubmodule (T : H →L[ℂ] K) (δ : ℝ) : Submodule ℂ H :=
  (cutoffPositivePart T δ).range.topologicalClosure

/-- Actual CFC data: positive parts, difference, and orthogonality. -/
theorem cutoffPositivePart_decomposition (T : H →L[ℂ] K) (δ : ℝ) :
    let D := T.adjoint.comp T - ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H
    (cutoffPositivePart T δ).IsPositive ∧ D⁻.IsPositive ∧
      D = cutoffPositivePart T δ - D⁻ ∧
      D⁻.comp (cutoffPositivePart T δ) = 0 := by
  dsimp only
  let D := T.adjoint.comp T - ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H
  have hconst : IsSelfAdjoint (((δ ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ H)) := by
    simp [IsSelfAdjoint, star_smul, star_eq_adjoint, adjoint_id]
  have hD : IsSelfAdjoint D := (isPositive_adjoint_comp_self T).isSelfAdjoint.sub hconst
  refine ⟨(nonneg_iff_isPositive).1 (CFC.posPart_nonneg D),
    (nonneg_iff_isPositive).1 (CFC.negPart_nonneg D),
    (CFC.posPart_sub_negPart D hD).symm, ?_⟩
  exact CFC.negPart_mul_posPart D

/-- The two order inequalities behind the cutoff, proved from the CFC
positive/negative decomposition. The squared threshold is explicit. -/
theorem cutoffPositivePart_order_bounds (T : H →L[ℂ] K) (δ : ℝ) :
    let R := cutoffPositivePart T δ
    ((δ ^ 2 : ℝ) : ℂ) • (R * R) ≤ R * (T.adjoint.comp T) * R ∧
      T.adjoint.comp T ≤ ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H + R := by
  dsimp only
  let Q := T.adjoint.comp T
  let D := Q - ((δ ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ H)
  let R := cutoffPositivePart T δ
  obtain ⟨hR, hN, hdec, hNR⟩ := cutoffPositivePart_decomposition T δ
  have hQ : Q = R - D⁻ + ((δ ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ H) :=
    (sub_eq_iff_eq_add).1 hdec
  have hRN : R * D⁻ = 0 := CFC.posPart_mul_negPart D
  have hN0 : 0 ≤ D⁻ := (nonneg_iff_isPositive).2 hN
  have hcube : 0 ≤ R * R * R := by
    apply (nonneg_iff_isPositive).2
    have hR' : R.IsPositive := hR
    have hc := hR'.adjoint_conj R
    change (R.adjoint.comp (R.comp R)).IsPositive at hc
    rw [hR'.isSymmetric.clm_adjoint_eq] at hc
    simpa only [mul_def, comp_assoc] using hc
  have hmul : R * Q * R = R * R * R + ((δ ^ 2 : ℝ) : ℂ) • (R * R) := by
    rw [hQ]
    change R * (R - D⁻ + ((δ ^ 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H)) * R = _
    simp only [mul_add, mul_sub, add_mul, sub_mul, hRN, zero_mul, sub_zero,
      mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  constructor
  · rw [hmul]
    exact le_add_of_nonneg_left hcube
  · calc
      Q = R - D⁻ + ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H := hQ
      _ ≤ R + ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H := by
        exact add_le_add (sub_le_self R hN0) le_rfl
      _ = ((δ ^ 2 : ℝ) : ℂ) • .id ℂ H + R := add_comm _ _

/-- The exact complement is the kernel of the positive cutoff part. -/
theorem orthogonal_cutoffSubmodule (T : H →L[ℂ] K) (δ : ℝ) :
    (cutoffSubmodule T δ)ᗮ = (cutoffPositivePart T δ).ker :=
  orthogonal_closure_range_eq_ker_of_isPositive _
    (cutoffPositivePart_decomposition T δ).1

/-- The cutoff submodule is closed in the original Hilbert norm. -/
theorem isClosed_cutoffSubmodule (T : H →L[ℂ] K) (δ : ℝ) :
    IsClosed (cutoffSubmodule T δ : Set H) :=
  (cutoffPositivePart T δ).range.isClosed_topologicalClosure

/-- Non-strict estimates with a common positive threshold, on complementary spaces. -/
theorem cutoffSubmodule_bounds (T : H →L[ℂ] K) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ cutoffSubmodule T δ, δ * ‖x‖ ≤ ‖T x‖) ∧
      (∀ x ∈ (cutoffSubmodule T δ)ᗮ, ‖T x‖ ≤ δ * ‖x‖) := by
  obtain ⟨hR, hN, hdec, hNR⟩ := cutoffPositivePart_decomposition T δ
  exact ⟨cutoff_lower_bound_of_positive_decomposition T hδ _ _ hR hdec hNR,
    cutoff_upper_bound_of_positive_decomposition T hδ _ _ hR hN hdec⟩

/-- The literal T-image of the cutoff subspace is closed when the threshold is positive. -/
theorem isClosed_image_cutoffSubmodule (T : H →L[ℂ] K) {δ : ℝ} (hδ : 0 < δ) :
    IsClosed (T '' (cutoffSubmodule T δ : Set H)) :=
  isClosed_image_submodule_of_lower_bound T _ (isClosed_cutoffSubmodule T δ)
    hδ (cutoffSubmodule_bounds T hδ.le).1

/-- Repaired two-threshold statement. At epsilon/2 there are non-strict vector
bounds; the complementary restriction therefore has operator norm strictly below epsilon. -/
theorem exists_closed_submodule_two_threshold_cutoff_complex
    (T : H →L[ℂ] K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Submodule ℂ H, IsClosed (S : Set H) ∧
      (∀ x ∈ S, (ε / 2) * ‖x‖ ≤ ‖T x‖) ∧
      (∀ x ∈ Sᗮ, ‖T x‖ ≤ (ε / 2) * ‖x‖) ∧
      ‖T.comp (Sᗮ).subtypeL‖ < ε ∧ IsClosed (T '' (S : Set H)) := by
  let S := cutoffSubmodule T (ε / 2)
  have hd : 0 < ε / 2 := half_pos hε
  obtain ⟨hl, hu⟩ := cutoffSubmodule_bounds T hd.le
  refine ⟨S, isClosed_cutoffSubmodule T _, hl, hu, ?_,
    isClosed_image_cutoffSubmodule T hd⟩
  have hb : ‖T.comp (Sᗮ).subtypeL‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ hd.le
    intro x
    exact hu x x.property
  exact hb.trans_lt (half_lt_self hε)

end Complex
end ContinuousLinearMap
