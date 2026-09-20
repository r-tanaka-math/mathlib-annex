import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.DyadicCFC
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.FiniteAverage

/-!
# The normalized real-part estimate without any bidual extension

For selfadjoint a,b, a second-order polynomial at the identity gives
|Re V(a,b)| <= (Re V(a^2,1)+Re V(1,b^2))/2.  All remainder estimates and the
positive small-parameter argument are explicit.  No differentiability API,
Arens regularity, state factorization, or spectral projection is assumed.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace MathlibAnnex.CStarBilinear.Analytic
open MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {D : Type v}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

/-- Polynomial 1 + i a - a^2/2; no exponential is required. -/
def quadraticUnit (a : A) : A := 1 + Complex.I • a - (1 / 2 : ℂ) • a ^ 2

/-- Exact fourth-order norm defect for a selfadjoint input. -/
theorem quadraticUnit_star_mul (a : A) (ha : IsSelfAdjoint a) :
    star (quadraticUnit a) * quadraticUnit a = 1 + (1 / 4 : ℂ) • a ^ 4 := by
  have hs : star (quadraticUnit a) = 1 - Complex.I • a - (1 / 2 : ℂ) • a ^ 2 := by
    simp [quadraticUnit, star_sub, star_add, star_smul, star_pow, ha.star_eq,
      Complex.star_def]
    simp only [sub_eq_add_neg]
  have h2 : a * a = a ^ 2 := by noncomm_ring
  have h3 : a * a ^ 2 = a ^ 3 := by noncomm_ring
  have h3' : a ^ 2 * a = a ^ 3 := by noncomm_ring
  have h4 : a ^ 2 * a ^ 2 = a ^ 4 := by noncomm_ring
  rw [hs, quadraticUnit]
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, h2, h3, h3', h4]
  simp only [smul_sub, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul]
  module

/-- Real scaling preserves selfadjointness; it is not asserted for complex scaling. -/
theorem isSelfAdjoint_real_smul (t : ℝ) (a : A) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (t • a) := by
  change star (t • a) = t • a
  simp [star_smul, ha.star_eq]

/-- A direct bound by a fourth-order scalar remainder, valid for every real t. -/
theorem norm_quadraticUnit_real_smul_le (a : A) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖quadraticUnit (t • a)‖ ≤ 1 + t ^ 4 * (‖a ^ 4‖ / 4) := by
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have hn : ‖quadraticUnit (t • a)‖ ^ 2 ≤ 1 + t ^ 4 * (‖a ^ 4‖ / 4) := by
    calc
      _ = ‖star (quadraticUnit (t • a)) * quadraticUnit (t • a)‖ := by
        rw [CStarRing.norm_star_mul_self]; ring
      _ = ‖(1 : A) + (1 / 4 : ℂ) • (t • a) ^ 4‖ :=
        congrArg norm (quadraticUnit_star_mul _ (isSelfAdjoint_real_smul t a ha))
      _ ≤ ‖(1 : A)‖ + ‖(1 / 4 : ℂ) • (t • a) ^ 4‖ := norm_add_le _ _
      _ = 1 + t ^ 4 * (‖a ^ 4‖ / 4) := by
        rw [smul_pow, norm_smul, norm_smul]
        norm_num [Real.norm_eq_abs, abs_of_nonneg ht4, ← abs_pow] <;> ring
  have hR : 0 ≤ t ^ 4 * (‖a ^ 4‖ / 4) := by positivity
  nlinarith [norm_nonneg (quadraticUnit (t • a)), sq_nonneg (t ^ 4 * (‖a ^ 4‖ / 4))]

/-- Bilinear evaluation has a uniform fourth-order error for |t|<=1. -/
theorem normalized_quadratic_value_le (V : A →L[ℂ] D →L[ℂ] ℂ) (hV : ‖V‖ ≤ 1)
    (a : A) (ha : IsSelfAdjoint a) (b : D) (hb : IsSelfAdjoint b)
    (t : ℝ) (ht : t ^ 4 ≤ 1) :
    ‖V (quadraticUnit (t • a)) (quadraticUnit (t • b))‖ ≤
      1 + t ^ 4 * (‖a ^ 4‖ / 4 + ‖b ^ 4‖ / 4 +
        (‖a ^ 4‖ / 4) * (‖b ^ 4‖ / 4)) := by
  let x := quadraticUnit (t • a)
  let y := quadraticUnit (t • b)
  let p : ℝ := ‖a ^ 4‖ / 4
  let q : ℝ := ‖b ^ 4‖ / 4
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht0 : 0 ≤ t ^ 4 := by positivity
  have hx : ‖x‖ ≤ 1 + t ^ 4 * p := norm_quadraticUnit_real_smul_le a ha t
  have hy : ‖y‖ ≤ 1 + t ^ 4 * q := norm_quadraticUnit_real_smul_le b hb t
  calc
    ‖V x y‖ ≤ ‖V x‖ * ‖y‖ := (V x).le_opNorm y
    _ ≤ (‖V‖ * ‖x‖) * ‖y‖ := mul_le_mul_of_nonneg_right (V.le_opNorm x) (norm_nonneg _)
    _ ≤ (1 * (1 + t ^ 4 * p)) * (1 + t ^ 4 * q) := by gcongr
    _ ≤ 1 + t ^ 4 * (p + q + p * q) := by
      have herr := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht)) (mul_nonneg hp hq)
      nlinarith [herr]

/-- Averaging t and -t cancels both odd degrees.  The retained quartic term has
coefficient t^4/2 because two evaluations are being added. -/
theorem quadratic_even_real_identity (V : A →L[ℂ] D →L[ℂ] ℂ)
    (h1 : V 1 1 = 1) (a : A) (b : D) (t : ℝ) :
    (V (quadraticUnit (t • a)) (quadraticUnit (t • b))).re +
      (V (quadraticUnit ((-t) • a)) (quadraticUnit ((-t) • b))).re =
      2 - t ^ 2 * ((V (a ^ 2) 1).re + (V 1 (b ^ 2)).re + 2 * (V a b).re) +
        (t ^ 4 / 2) * (V (a ^ 2) (b ^ 2)).re := by
  simp only [quadraticUnit, smul_pow, map_sub, map_add, map_smul,
    ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, h1,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow] <;> ring

/-- A positive cutoff proves the vanishing of a quadratic error.  t=0 is never
substituted into a cancelled factor, and no moment is divided by. -/
theorem le_zero_of_small_quadratic_errors (x K : ℝ) (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → x ≤ t ^ 2 * K) : x ≤ 0 := by
  by_contra hx
  have hx0 : 0 < x := lt_of_not_ge hx
  let d : ℝ := 2 * (K + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let t : ℝ := min 1 (x / d)
  have ht : 0 < t := lt_min (by norm_num) (div_pos hx0 hd)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t ≤ x / d := min_le_right _ _
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  have hsmall : x ≤ (x / d) * K :=
    (h t ht ht1).trans ((mul_le_mul_of_nonneg_right ht2 hK).trans
      (mul_le_mul_of_nonneg_right htd hK))
  have he : (x / d) * d = x := by field_simp [ne_of_gt hd]
  have hm := mul_le_mul_of_nonneg_right hsmall hd.le
  have he' : ((x / d) * K) * d = x * K := by
    calc _ = ((x / d) * d) * K := by ring
         _ = x * K := by rw [he]
  rw [he'] at hm
  dsimp [d] at hm
  nlinarith [mul_nonneg hx0.le hK]

/-- One sign of the real-part bound, obtained entirely from the norm inequality. -/
theorem normalized_neg_re_le_half (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (b : D) (hb : IsSelfAdjoint b) :
    -(V a b).re ≤ ((V (a ^ 2) 1).re + (V 1 (b ^ 2)).re) / 2 := by
  let m := (V (a ^ 2) 1).re
  let n := (V 1 (b ^ 2)).re
  let r := (V a b).re
  let w := (V (a ^ 2) (b ^ 2)).re
  let K := ‖a ^ 4‖ / 4 + ‖b ^ 4‖ / 4 + (‖a ^ 4‖ / 4) * (‖b ^ 4‖ / 4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx : -(m + n + 2 * r) ≤ 0 := by
    apply le_zero_of_small_quadratic_errors _ (2 * K + |w|) (by positivity)
    intro t ht ht1
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have ht4 : t ^ 4 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)]
    have hp := normalized_quadratic_value_le V hV a ha b hb t ht4
    have hm := normalized_quadratic_value_le V hV a ha b hb (-t) (by nlinarith)
    have hreP := Complex.re_le_norm (V (quadraticUnit (t • a)) (quadraticUnit (t • b)))
    have hreM := Complex.re_le_norm (V (quadraticUnit ((-t) • a)) (quadraticUnit ((-t) • b)))
    have he := quadratic_even_real_identity V h1 a b t
    change _ ≤ 1 + t ^ 4 * K at hp
    change _ ≤ 1 + (-t) ^ 4 * K at hm
    change _ = 2 - t ^ 2 * (m + n + 2 * r) + (t ^ 4 / 2) * w at he
    have hw : 0 ≤ w / 2 + |w| := by nlinarith [neg_le_abs w, abs_nonneg w]
    have herr := mul_nonneg (show 0 ≤ t ^ 4 by positivity) hw
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp
    nlinarith [hp, hm, hreP, hreM, he, herr]
  change -r ≤ (m + n) / 2
  linarith

/-- Real-part additive bound.  No strictly positive second-moment assumption. -/
theorem normalized_abs_re_le_half (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (b : D) (hb : IsSelfAdjoint b) :
    |(V a b).re| ≤ ((leftMarginal V (a ^ 2)).re + (rightMarginal V (b ^ 2)).re) / 2 := by
  have hminus := normalized_neg_re_le_half V hV h1 a ha b hb
  have hplus := normalized_neg_re_le_half V hV h1 a ha (-b) hb.neg
  simp only [map_neg, Complex.neg_re, neg_neg, neg_sq] at hplus
  exact abs_le.mpr ⟨by simpa only [leftMarginal_apply, rightMarginal_apply, neg_neg] using neg_le_neg hminus,
    by simpa only [leftMarginal_apply, rightMarginal_apply] using hplus⟩

end MathlibAnnex.CStarBilinear.Analytic
