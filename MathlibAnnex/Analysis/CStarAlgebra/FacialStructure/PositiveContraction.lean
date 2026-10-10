/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Tactic

/-!
# A positive contraction with a represented unit fixed vector

A nonzero star representation has a nonzero represented self-adjoint element `b`.
Put `r = ‖pi b‖ / 2`, let `q` clip the real line to `[-r,r]`, and put
`f(t) = min (|t|,r) / r`, `g(t) = t - q(t)`. Then `f g = g`, `0 ≤ f ≤ 1`,
and both functions vanish at zero. Nonunital functional calculus produces
`e d = d` in the original algebra. Contractivity and `‖q(b)‖ ≤ r` imply
`pi d ≠ 0`. A normalized nonzero vector in its range is fixed by `pi e`.

This argument neither chooses an eigenvalue of `pi b` nor assumes that any
nonzero projection or rank-one operator belongs to the algebra or its image.
-/

set_option autoImplicit false

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra
namespace NonUnitalCStarRepresentation

variable {A H : Type*} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Even before irreducibility, a nonzero representation admits a positive
contraction in the original algebra with a represented unit fixed vector. -/
theorem exists_nonneg_norm_le_one_and_exists_norm_eq_one_apply_eq_self
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsNonzero) :
    ∃ e : A, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧
      ∃ xi : H, ‖xi‖ = 1 ∧ pi e xi = xi := by
  classical
  obtain ⟨a, ha⟩ := hpi
  let b : A := star a * a
  have hb : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
  have hbne : pi b ≠ 0 := by
    simpa only [b, map_mul, map_star, ne_eq, CStarRing.star_mul_self_eq_zero_iff] using ha
  let r : ℝ := ‖pi b‖ / 2
  have hr : 0 < r := half_pos (norm_pos_iff.mpr hbne)
  let q : ℝ → ℝ := fun t => max (-r) (min r t)
  let f : ℝ → ℝ := fun t => min |t| r / r
  let g : ℝ → ℝ := fun t => t - q t
  have hq : Continuous q := continuous_const.max (continuous_const.min continuous_id)
  have hf : Continuous f := (continuous_id.abs.min continuous_const).div_const r
  have hg : Continuous g := continuous_id.sub hq
  have hq0 : q 0 = 0 := by simp [q, hr.le]
  have hf0 : f 0 = 0 := by simp [f, hr.le]
  have hg0 : g 0 = 0 := by simp [g, hq0]
  have hf_nonneg (t : ℝ) : 0 ≤ f t :=
    div_nonneg (le_min (abs_nonneg t) hr.le) hr.le
  have hf_le (t : ℝ) : f t ≤ 1 := by
    exact (div_le_one hr).2 (min_le_right |t| r)
  have hq_bound (t : ℝ) : ‖q t‖ ≤ r := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [hr]) (min_le_left _ _)⟩
  have hfg (t : ℝ) : f t * g t = g t := by
    by_cases ht : |t| ≤ r
    · have hqt : q t = t := by
        dsimp only [q]
        rw [min_eq_right (abs_le.mp ht).2, max_eq_right (abs_le.mp ht).1]
      simp [g, hqt]
    · have hft : f t = 1 := by
        dsimp only [f]
        rw [min_eq_right (lt_of_not_ge ht).le, div_self hr.ne']
      rw [hft, one_mul]
  let e : A := cfcₙ (p := IsSelfAdjoint) f b
  let d : A := cfcₙ (p := IsSelfAdjoint) g b
  have he : 0 ≤ e := cfcₙ_nonneg fun t _ => hf_nonneg t
  have henorm : ‖e‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg t)]
    exact hf_le t
  have hcut : ‖cfcₙ (p := IsSelfAdjoint) q b‖ ≤ r :=
    norm_cfcₙ_le fun t _ => hq_bound t
  have hd : d = b - cfcₙ (p := IsSelfAdjoint) q b := by
    change cfcₙ (fun t : ℝ => t - q t) b = _
    rw [cfcₙ_sub (fun t : ℝ => t) q b continuousOn_id (by rfl)
      hq.continuousOn hq0, cfcₙ_id' ℝ b hb]
  have hed : e * d = d := by
    calc
      e * d = cfcₙ (fun t : ℝ => f t * g t) b :=
        (cfcₙ_mul f g b hf.continuousOn hf0 hg.continuousOn hg0).symm
      _ = d := cfcₙ_congr fun t _ => hfg t
  have hdne : pi d ≠ 0 := by
    intro hz
    have heq : pi b = pi (cfcₙ (p := IsSelfAdjoint) q b) := by
      apply sub_eq_zero.mp
      simpa only [hd, map_sub] using hz
    have hnorm : ‖pi b‖ ≤ r := by
      rw [heq]
      exact (NonUnitalStarAlgHom.norm_apply_le pi _).trans hcut
    have hpos : 0 < ‖pi b‖ := norm_pos_iff.mpr hbne
    dsimp only [r] at hnorm
    linarith
  obtain ⟨z, hz⟩ : ∃ z : H, pi d z ≠ 0 := by
    by_contra! hall
    exact hdne (ContinuousLinearMap.ext fun z => hall z)
  have hzpos : 0 < ‖pi d z‖ := norm_pos_iff.mpr hz
  let xi : H := ((‖pi d z‖ : ℂ)⁻¹) • pi d z
  have hxi : ‖xi‖ = 1 := by
    simp only [xi, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hzpos, inv_mul_cancel₀ hzpos.ne']
  have hfixed : pi e (pi d z) = pi d z := by
    have hvalue := congrArg (fun t : A => pi t z) hed
    simpa only [map_mul, ContinuousLinearMap.mul_apply] using hvalue
  refine ⟨e, he, henorm, xi, hxi, ?_⟩
  simpa only [xi, map_smul, hfixed]

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
