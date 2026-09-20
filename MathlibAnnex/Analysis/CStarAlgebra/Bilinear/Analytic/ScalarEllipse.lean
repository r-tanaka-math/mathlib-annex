import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The scalar ellipse forced by two independent unit phases

This is an elementary finite-dimensional optimization proof.  It makes no
reference to weak compactness, Arens extensions, or a bilinear factorization.
The marginal endpoint cases are included: there is no division by a marginal
state value or by its complement.  SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarBilinear.Analytic

/-- A real linear functional on the complex unit circle attains its Euclidean
support value.  The zero vector is treated before normalizing. -/
theorem exists_unit_support (a b : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      a * z.re + b * z.im = Real.sqrt (a ^ 2 + b ^ 2) := by
  let r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  by_cases hr : r = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    refine ⟨1, norm_one, ?_⟩
    simp [ha, hb]
  · let z : ℂ := ⟨a / r, b / r⟩
    have hzsq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change (a / r) * (a / r) + (b / r) * (b / r) = 1
      field_simp [hr]
      nlinarith [hrsq]
    refine ⟨z, ?_, ?_⟩
    · nlinarith [norm_nonneg z]
    · change a * (a / r) + b * (b / r) = r
      field_simp [hr]
      nlinarith [hrsq]

/-- Algebraic extraction of an ellipse bound from the sum of its focal radii.
No bounds on `g` or `d` are assumed separately. -/
theorem ellipse_of_radius_sum (g d e r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrsq : r ^ 2 = (g + d) ^ 2 + e ^ 2)
    (hssq : s ^ 2 = (g - d) ^ 2 + e ^ 2)
    (hrs : r + s ≤ 2) :
    e ^ 2 ≤ (1 - g ^ 2) * (1 - d ^ 2) := by
  have hlow : 0 ≤ 4 - r ^ 2 - s ^ 2 - 2 * r * s := by
    have ht := mul_nonneg (sub_nonneg.mpr hrs)
      (show 0 ≤ 2 + (r + s) by linarith)
    nlinarith
  have hhigh : 0 ≤ 4 - r ^ 2 - s ^ 2 + 2 * r * s := by
    nlinarith [mul_nonneg hr hs]
  have hproduct := mul_nonneg hlow hhigh
  have hidentity :
      (4 - r ^ 2 - s ^ 2 - 2 * r * s) *
        (4 - r ^ 2 - s ^ 2 + 2 * r * s) =
      16 * ((1 - g ^ 2) * (1 - d ^ 2) - e ^ 2) := by
    calc
      _ = (4 - r ^ 2 - s ^ 2) ^ 2 - 4 * r ^ 2 * s ^ 2 := by ring
      _ = 16 * ((1 - g ^ 2) * (1 - d ^ 2) - e ^ 2) := by
        rw [hrsq, hssq]
        ring
  rw [hidentity] at hproduct
  nlinarith

/-- Two independently chosen unit phases force the exact ellipse bound.
Only a one-sided upper bound is needed, because the maximizing phases are
chosen explicitly by `exists_unit_support`. -/
theorem ellipse_of_unit_phase_test (g d e : ℝ)
    (h : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 →
      (g + d) * z.im - (g - d) * w.im +
          e * (z.re - w.re) ≤ 2) :
    e ^ 2 ≤ (1 - g ^ 2) * (1 - d ^ 2) := by
  obtain ⟨z, hz, hzs⟩ := exists_unit_support e (g + d)
  obtain ⟨w, hw, hws⟩ := exists_unit_support (-e) (d - g)
  have ht := h z w hz hw
  have hsum : Real.sqrt (e ^ 2 + (g + d) ^ 2) +
      Real.sqrt ((-e) ^ 2 + (d - g) ^ 2) ≤ 2 := by
    nlinarith [hzs, hws]
  apply ellipse_of_radius_sum g d e
    (Real.sqrt (e ^ 2 + (g + d) ^ 2))
    (Real.sqrt ((-e) ^ 2 + (d - g) ^ 2))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [Real.sq_sqrt (by positivity)]
    ring
  · rw [Real.sq_sqrt (by positivity)]
    ring
  · exact hsum

/-- Translation to the marginal coordinates used by a normalized bilinear
form.  It includes `s = 0`, `s = 1`, `t = 0`, and `t = 1`. -/
theorem covariance_bound_of_unit_phase_test (s t b : ℝ)
    (h : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 →
      ((2 * s - 1) + (2 * t - 1)) * z.im -
        ((2 * s - 1) - (2 * t - 1)) * w.im +
        (4 * b) * (z.re - w.re) ≤ 2) :
    b ^ 2 ≤ s * (1 - s) * t * (1 - t) := by
  have he := ellipse_of_unit_phase_test (2 * s - 1) (2 * t - 1) (4 * b) h
  have hi :
      (1 - (2 * s - 1) ^ 2) * (1 - (2 * t - 1) ^ 2) =
      16 * (s * (1 - s) * t * (1 - t)) := by ring
  rw [hi] at he
  nlinarith

/-- The scalar value of the two-phase test after unit-phase cancellations. -/
def phasePolynomial (u : ℂ) (s t : ℝ) (z w : ℂ) : ℂ :=
  z * u + star w * ((s : ℂ) - u) + w * ((t : ℂ) - u) +
    star z * (1 - (s : ℂ) - (t : ℂ) + u)

/-- Exact imaginary-part calculation; the real part of `u` cancels. -/
theorem twice_im_phasePolynomial (u : ℂ) (s t : ℝ) (z w : ℂ) :
    2 * (phasePolynomial u s t z w).im =
      ((2 * s - 1) + (2 * t - 1)) * z.im -
        ((2 * s - 1) - (2 * t - 1)) * w.im +
        (4 * u.im) * (z.re - w.re) := by
  simp only [phasePolynomial, Complex.add_im, Complex.sub_im, Complex.add_re,
    Complex.sub_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_im, Complex.one_re]
  ring

/-- The analytic input to the scalar ellipse is only contractivity of the
explicit phase polynomial, not a Grothendieck inequality. -/
theorem covariance_of_phasePolynomial_bound (u : ℂ) (s t : ℝ)
    (h : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 →
      ‖phasePolynomial u s t z w‖ ≤ 1) :
    u.im ^ 2 ≤ s * (1 - s) * t * (1 - t) := by
  apply covariance_bound_of_unit_phase_test s t u.im
  intro z w hz hw
  rw [← twice_im_phasePolynomial]
  have hi : (phasePolynomial u s t z w).im ≤ 1 :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (h z w hz hw))
  linarith

end MathlibAnnex.CStarBilinear.Analytic
