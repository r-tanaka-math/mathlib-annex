/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Escape from finite-dimensional subspaces and vanishing of compact operators

These three Hilbert-space lemmas have no GSS or representation hypotheses.
The existing compact adjoint and approximation API is reused unchanged.
The supplied statements are complex Hilbert endomorphism statements.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace ContinuousLinearMap

universe v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The distance from a noncompact operator to the original compact submodule is positive. -/
theorem infDist_compactOperator_pos {T : H →L[ℂ] H} (hT : ¬ IsCompactOperator T) :
    0 < Metric.infDist T (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H)) := by
  exact (isClosed_setOf_isCompactOperator.notMem_iff_infDist_pos
    ⟨0, isCompactOperator_zero⟩).1 hT

/-- Outside every finite-dimensional subspace there is a unit vector on which a
noncompact operator stays above half its distance from the compact operators. -/
theorem exists_norm_eq_one_mem_orthogonal_norm_apply_gt_infDist
    (T : H →L[ℂ] H) (hT : ¬ IsCompactOperator T)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M] :
    ∃ x : H, x ∈ Mᗮ ∧ ‖x‖ = 1 ∧
      Metric.infDist T (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H)) / 2 <
        ‖T x‖ := by
  letI : CompleteSpace M := FiniteDimensional.complete ℂ M
  let d : ℝ := Metric.infDist T
    (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H))
  have hd : 0 < d := infDist_compactOperator_pos hT
  have hP : IsCompactOperator M.starProjection := by
    letI : FiniteDimensional ℂ M.starProjection.range := by
      rw [Submodule.range_starProjection]
      infer_instance
    exact M.starProjection.isCompactOperator_of_finiteDimensional_range
  have hTP : IsCompactOperator (T.comp M.starProjection) := hP.clm_comp T
  have hdist : d ≤ ‖T - T.comp M.starProjection‖ := by
    exact (Metric.infDist_le_dist_of_mem (x := T)
      (s := (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H)))
      (y := T.comp M.starProjection) hTP).trans_eq (dist_eq_norm _ _)
  obtain ⟨z, hz⟩ : ∃ z : H,
      d / 2 * ‖z‖ < ‖(T - T.comp M.starProjection) z‖ := by
    by_contra! h
    have hnorm : ‖T - T.comp M.starProjection‖ ≤ d / 2 :=
      (T - T.comp M.starProjection).opNorm_le_bound (by positivity) h
    linarith
  let y : H := z - M.starProjection z
  have hym : y ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal z
  have hyn : ‖y‖ ≤ ‖z‖ := by
    simpa only [y, Submodule.starProjection_orthogonal_val] using
      Mᗮ.norm_starProjection_apply_le z
  have hzy : (T - T.comp M.starProjection) z = T y := by
    simp only [y, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [hzy] at hz
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, map_zero, norm_zero] at hz
    exact (mul_nonneg (by positivity : 0 ≤ d / 2) (norm_nonneg z)).not_gt hz
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  let x : H := ((‖y‖ : ℂ)⁻¹) • y
  have hxn : ‖x‖ = 1 := by
    simp [x, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hyp, hyp.ne']
  have hvalue : ‖T x‖ = ‖T y‖ / ‖y‖ := by
    simp only [x, map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hyp, div_eq_mul_inv, mul_comm]
  refine ⟨x, Mᗮ.smul_mem _ hym, hxn, ?_⟩
  change d / 2 < ‖T x‖
  rw [hvalue]
  exact (lt_div_iff₀ hyp).2
    ((mul_le_mul_of_nonneg_left hyn (by positivity : 0 ≤ d / 2)).trans_lt hz)

/-- Compact operators vanish along any net of bounded vectors orthogonal to the
indexing finite-dimensional subspace. This net is not assumed countable. -/
theorem tendsto_apply_zero_of_isCompactOperator_of_mem_orthogonal
    (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (x : {M : Submodule ℂ H // FiniteDimensional ℂ M} → H)
    (hx : ∀ M : {M : Submodule ℂ H // FiniteDimensional ℂ M}, x M ∈ M.valᗮ)
    (hn : ∀ M : {M : Submodule ℂ H // FiniteDimensional ℂ M}, ‖x M‖ ≤ 1) :
    Tendsto (fun M => T (x M)) atTop (𝓝 0) := by
  letI : Nonempty {M : Submodule ℂ H // FiniteDimensional ℂ M} :=
    ⟨⟨⊥, inferInstance⟩⟩
  letI : IsDirectedOrder {M : Submodule ℂ H // FiniteDimensional ℂ M} := by
    refine ⟨?_⟩
    intro M N
    letI : FiniteDimensional ℂ M.val := M.property
    letI : FiniteDimensional ℂ N.val := N.property
    refine ⟨⟨M.val ⊔ N.val, inferInstance⟩, ?_, ?_⟩
    · change M.val ≤ M.val ⊔ N.val
      exact le_sup_left
    · change N.val ≤ M.val ⊔ N.val
      exact le_sup_right
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF, hTF⟩ := hT.adjoint.exists_finiteDimensional_range_norm_sub_lt hε
  have hnorm : ‖T - F.adjoint‖ < ε := by
    calc
      ‖T - F.adjoint‖ = ‖(T.adjoint - F).adjoint‖ := by
        rw [map_sub, ContinuousLinearMap.adjoint_adjoint]
      _ = ‖T.adjoint - F‖ := ContinuousLinearMap.adjoint.norm_map _
      _ < ε := hTF
  filter_upwards [eventually_ge_atTop
    (⟨F.range, hF⟩ : {M : Submodule ℂ H // FiniteDimensional ℂ M})] with M hM
  have hzero : F.adjoint (x M) = 0 := by
    apply ext_inner_right ℂ
    intro z
    rw [inner_zero_left, ContinuousLinearMap.adjoint_inner_left]
    exact inner_eq_zero_symm.mp ((hx M) (F z) (hM ⟨z, rfl⟩))
  rw [dist_zero_right]
  calc
    ‖T (x M)‖ = ‖(T - F.adjoint) (x M)‖ := by
      rw [ContinuousLinearMap.sub_apply, hzero, sub_zero]
    _ ≤ ‖T - F.adjoint‖ * ‖x M‖ := (T - F.adjoint).le_opNorm _
    _ ≤ ‖T - F.adjoint‖ * 1 :=
      mul_le_mul_of_nonneg_left (hn M) (norm_nonneg _)
    _ < ε := by simpa only [mul_one] using hnorm

end ContinuousLinearMap

