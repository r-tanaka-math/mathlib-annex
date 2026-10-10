/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CoefficientTranslate
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic

/-!
# Irreducibility of a cyclic realization of an extreme coefficient

Suppose a unit-norm extreme dual functional is realized as a coefficient of
two unit vectors, and the source vector is cyclic for the original algebra.
A reducing projection splits the coefficient into two pieces. Equality in
the two norm estimates makes the squared projection norms convex weights.
Extremality then makes one projected coefficient proportional to the whole
coefficient. Cyclicity transfers that identity to the output vector, so the
projection has eigenvalue equal to its convex weight. Idempotence rules out
a weight strictly between zero and one.

The cyclic norm-preserving realization is a hypothesis of this criterion,
not an existence theorem for arbitrary extreme functionals.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A norm-preserving extreme coefficient with a cyclic source vector has
an irreducible realization. Nonzeroness is proved from the coefficient norm. -/
theorem isIrreducible_of_extreme_matrixCoefficient_of_denseRange
    (pi : NonUnitalCStarRepresentation A H) (x y : H)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hnorm : ‖matrixCoefficient pi x y‖ = 1)
    (hext : matrixCoefficient pi x y ∈
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hcyclic : DenseRange (fun a : A => pi a x)) : pi.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · change ∃ a : A, pi a ≠ 0
    by_contra! hall
    have hfzero : matrixCoefficient pi x y = 0 := by
      ext a
      simp only [matrixCoefficient_apply, hall, ContinuousLinearMap.zero_apply, inner_zero_right]
    rw [hfzero, norm_zero] at hnorm
    norm_num at hnorm
  · intro M hM
    letI : IsClosed (M : Set H) := hM.1
    letI : CompleteSpace M := inferInstance
    letI : M.HasOrthogonalProjection := inferInstance
    let P : H →L[ℂ] H := M.starProjection
    have hPcomm (a : A) (z : H) : P (pi a z) = pi a (P z) := by
      have h := Representation.starProjection_commutes_of_reduces pi.unitization M
        (reduces_unitization_of_reduces pi M hM) (Unitization.inr a)
      simpa only [unitization_inr, ContinuousLinearMap.mul_apply] using
        congrArg (fun T : H →L[ℂ] H => T z) h
    let x0 := P x
    let x1 := x - x0
    let y0 := P y
    let y1 := y - y0
    have hx0M : x0 ∈ M := M.starProjection_apply_mem x
    have hy0M : y0 ∈ M := M.starProjection_apply_mem y
    have hx1M : x1 ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
    have hy1M : y1 ∈ Mᗮ := M.sub_starProjection_mem_orthogonal y
    have hmap0 (a : A) : pi a x0 ∈ M := (hM.2 a x0 hx0M).1
    have hmap1 (a : A) : pi a x1 ∈ Mᗮ :=
      Representation.map_mem_orthogonal_of_adjoint_mem (pi a) M
        (fun z hz => (hM.2 a z hz).2) hx1M
    by_cases hx0 : x0 = 0
    · left
      have hPzero : P = 0 := by
        apply ContinuousLinearMap.ext
        intro z
        exact hcyclic.induction_on z (isClosed_eq P.continuous continuous_const) fun a => by
          rw [hPcomm]
          change pi a x0 = 0
          rw [hx0, map_zero]
      rw [← M.range_starProjection, show M.starProjection = 0 from hPzero]
      simp
    by_cases hx1 : x1 = 0
    · right
      have hPx : P x = x := (sub_eq_zero.mp hx1).symm
      have hPone : P = 1 := by
        apply ContinuousLinearMap.ext
        intro z
        exact hcyclic.induction_on z (isClosed_eq P.continuous continuous_id) fun a => by
          rw [hPcomm, hPx]
          rfl
      rw [← M.range_starProjection, show M.starProjection = 1 from hPone]
      exact LinearMap.range_eq_top.mpr fun z => ⟨z, rfl⟩
    exfalso
    have norm_split (z : H) : ‖z‖ ^ 2 = ‖P z‖ ^ 2 + ‖z - P z‖ ^ 2 := by
      have horth := M.inner_right_of_mem_orthogonal
        (M.starProjection_apply_mem z) (M.sub_starProjection_mem_orthogonal z)
      have h := norm_add_sq (𝕜 := ℂ) (P z) (z - P z)
      rw [show P z + (z - P z) = z by abel, horth] at h
      simpa only [RCLike.zero_re, mul_zero, add_zero] using h
    have hxn : ‖x0‖ ^ 2 + ‖x1‖ ^ 2 = 1 := by
      simpa only [x0, x1, hx, one_pow] using (norm_split x).symm
    have hyn : ‖y0‖ ^ 2 + ‖y1‖ ^ 2 = 1 := by
      simpa only [y0, y1, hy, one_pow] using (norm_split y).symm
    let f := matrixCoefficient pi x y
    let f0 := matrixCoefficient pi x0 y0
    let f1 := matrixCoefficient pi x1 y1
    have hxdecomp : x = x0 + x1 := by dsimp only [x1]; abel
    have hydecomp : y = y0 + y1 := by dsimp only [y1]; abel
    have hdecomp : f0 + f1 = f := by
      apply ContinuousLinearMap.ext
      intro a
      change inner ℂ y0 (pi a x0) + inner ℂ y1 (pi a x1) = inner ℂ y (pi a x)
      rw [hydecomp, hxdecomp, map_add, inner_add_left, inner_add_right, inner_add_right,
        M.inner_right_of_mem_orthogonal hy0M (hmap1 a),
        M.inner_left_of_mem_orthogonal (hmap0 a) hy1M, add_zero, zero_add]
    have hlower : 1 ≤ ‖x0‖ * ‖y0‖ + ‖x1‖ * ‖y1‖ := by
      calc
        1 = ‖f‖ := hnorm.symm
        _ = ‖f0 + f1‖ := congrArg norm hdecomp.symm
        _ ≤ ‖f0‖ + ‖f1‖ := norm_add_le _ _
        _ ≤ ‖x0‖ * ‖y0‖ + ‖x1‖ * ‖y1‖ :=
          add_le_add (norm_matrixCoefficient_le pi x0 y0) (norm_matrixCoefficient_le pi x1 y1)
    have hsq0 : (‖x0‖ - ‖y0‖) ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖x0‖ - ‖y0‖), sq_nonneg (‖x1‖ - ‖y1‖)]
    have hsq1 : (‖x1‖ - ‖y1‖) ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖x0‖ - ‖y0‖), sq_nonneg (‖x1‖ - ‖y1‖)]
    have hsame0 : ‖y0‖ = ‖x0‖ := (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)).symm
    have hsame1 : ‖y1‖ = ‖x1‖ := (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq1)).symm
    let s : ℝ := ‖x0‖ ^ 2
    let t : ℝ := ‖x1‖ ^ 2
    have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have ht : 0 < t := sq_pos_of_pos (norm_pos_iff.mpr hx1)
    have hst : s + t = 1 := hxn
    have hb0 : ‖f0‖ ≤ s := by
      simpa only [s, hsame0, pow_two] using norm_matrixCoefficient_le pi x0 y0
    have hb1 : ‖f1‖ ≤ t := by
      simpa only [t, hsame1, pow_two] using norm_matrixCoefficient_le pi x1 y1
    let g0 : StrongDual ℂ A := s⁻¹ • f0
    let g1 : StrongDual ℂ A := t⁻¹ • f1
    have hg0 : g0 ∈ closedBall (0 : StrongDual ℂ A) 1 := by
      apply mem_closedBall_zero_iff.mpr
      calc
        ‖g0‖ = s⁻¹ * ‖f0‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
        _ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hb0 (inv_nonneg.mpr hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    have hg1 : g1 ∈ closedBall (0 : StrongDual ℂ A) 1 := by
      apply mem_closedBall_zero_iff.mpr
      calc
        ‖g1‖ = t⁻¹ * ‖f1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
        _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hb1 (inv_nonneg.mpr ht.le)
        _ = 1 := inv_mul_cancel₀ ht.ne'
    have hcomb : s • g0 + t • g1 = f := by
      simpa only [g0, g1, smul_smul, mul_inv_cancel₀ hs.ne',
        mul_inv_cancel₀ ht.ne', one_smul] using hdecomp
    have heq : g0 = f := hext.2 hg0 hg1 ⟨s, t, hs, ht, hst, hcomb⟩
    have hf0 : f0 = s • f := by
      calc
        f0 = s • g0 := by simp only [g0, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
        _ = s • f := by rw [heq]
    have hfirst (a : A) : inner ℂ y0 (pi a x) = f0 a := by
      change inner ℂ y0 (pi a x) = inner ℂ y0 (pi a x0)
      rw [hxdecomp, map_add, inner_add_right,
        M.inner_right_of_mem_orthogonal hy0M (hmap1 a), add_zero]
    have hPy : P y = s • y := by
      apply ext_inner_right ℂ
      intro z
      exact hcyclic.induction_on z
        (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id))
        fun a => by
          change inner ℂ y0 (pi a x) = inner ℂ (s • y) (pi a x)
          rw [hfirst, hf0]
          change s • inner ℂ y (pi a x) = inner ℂ (s • y) (pi a x)
          exact (inner_smul_left_eq_smul y (pi a x) s).symm
    have hyne : y ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hy
      norm_num at hy
    have hidem := congrArg (fun T : H →L[ℂ] H => T y) M.isIdempotentElem_starProjection.eq
    change P (P y) = P y at hidem
    rw [hPy, ContinuousLinearMap.map_smul_of_tower, hPy] at hidem
    have hss : s * s = s := smul_left_injective ℝ hyne (by simpa only [smul_smul] using hidem)
    nlinarith

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
