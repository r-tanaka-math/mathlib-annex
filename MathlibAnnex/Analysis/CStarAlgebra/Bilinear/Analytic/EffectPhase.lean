import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.ScalarEllipse

/-!
# Unit phases on positive contractions

The norm calculation does not use idempotency.  This is the replacement for
spectral projections in the first analytic step.  The order instances are
exactly the pre-existing C*-algebra interfaces.  No bidual algebra instance
is declared.  SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear.Analytic

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A two-phase affine combination of an effect and its complement. -/
def effectPhase (p : A) (z w : ℂ) : A := z • p + w • (1 - p)

/-- Positivity of the defect of an effect is proved by real CFC, not by a
false rule asserting positivity of arbitrary noncommuting products. -/
theorem effect_defect_nonneg (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p * (1 - p) := by
  have hsa : IsSelfAdjoint p := IsSelfAdjoint.of_nonneg hp
  have hup : ∀ r ∈ spectrum ℝ p, r ≤ 1 :=
    (le_algebraMap_iff_spectrum_le (R := ℝ) (r := 1) hsa).mp (by simpa using hp1)
  have hc : 0 ≤ cfc (fun r : ℝ ↦ r * (1 - r)) p := by
    apply cfc_nonneg
    intro r hr
    exact mul_nonneg (spectrum_nonneg_of_nonneg hp hr) (sub_nonneg.mpr (hup r hr))
  have hid : cfc (fun r : ℝ ↦ r) p = p := cfc_id' ℝ p hsa
  have hone : cfc (fun _ : ℝ ↦ 1) p = 1 := by
    simpa using cfc_const (1 : ℝ) p hsa
  rw [cfc_mul (fun r : ℝ => r) (fun r => 1 - r) p (by fun_prop) (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun r => r) p (by fun_prop) (by fun_prop),
    hid, hone] at hc
  exact hc

/-- Scalar unit-norm identity, exposed to make the phase cancellation exact. -/
theorem star_mul_unit_scalar (z : ℂ) (hz : ‖z‖ = 1) : star z * z = 1 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hz
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.one_im]
    ring

/-- Exact real cross coefficient for two unit phases. -/
theorem unit_scalar_cross (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    star z * w + star w * z = ((2 - ‖z - w‖ ^ 2 : ℝ) : ℂ) := by
  have hzs : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hz
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith
  have hws : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hw
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith
  · simp only [Complex.add_im, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- The identity behind effect contractivity, including arbitrary nonprojection
positive contractions. -/
theorem effectPhase_star_mul (p : A) (hp : IsSelfAdjoint p)
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    star (effectPhase p z w) * effectPhase p z w =
      1 - (‖z - w‖ ^ 2 : ℝ) • (p * (1 - p)) := by
  let q : A := 1 - p
  have hq : IsSelfAdjoint q := by
    change star (1 - p) = 1 - p
    rw [star_sub, star_one, hp.star_eq]
  have hcomm : q * p = p * q := by dsimp [q]; noncomm_ring
  have hsum : p * p + (p * q + p * q) + q * q = 1 := by
    dsimp [q]
    noncomm_ring
  have hexpand : star (effectPhase p z w) * effectPhase p z w =
      (star z * z) • (p * p) +
        (star z * w + star w * z) • (p * q) +
        (star w * w) • (q * q) := by
    change star (z • p + w • q) * (z • p + w • q) = _
    simp only [star_add, star_smul, hp.star_eq, hq.star_eq, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, add_smul]
    rw [hcomm]
    simp only [mul_comm z (star z), mul_comm z (star w),
      mul_comm w (star z), mul_comm w (star w)]
    abel
  rw [hexpand, star_mul_unit_scalar z hz, star_mul_unit_scalar w hw,
    unit_scalar_cross z w hz hw, one_smul, one_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  simp only [sub_smul, two_smul]
  calc
    _ = (p * p + (p * q + p * q) + q * q) -
        ((‖z - w‖ : ℂ) ^ 2) • (p * q) := by abel_nf
    _ = _ := by rw [hsum]; rfl

/-- A unit-phase affine combination of an effect is a contraction.  No
projection hypothesis, representation, or extension theorem is needed. -/
theorem norm_effectPhase_le_one (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖effectPhase p z w‖ ≤ 1 := by
  have hdef : 0 ≤ (‖z - w‖ ^ 2 : ℝ) • (p * (1 - p)) :=
    smul_nonneg (sq_nonneg _) (effect_defect_nonneg p hp hp1)
  have hle : star (effectPhase p z w) * effectPhase p z w ≤ 1 := by
    rw [effectPhase_star_mul p (IsSelfAdjoint.of_nonneg hp) z w hz hw]
    exact sub_le_self _ hdef
  have hn : ‖star (effectPhase p z w) * effectPhase p z w‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mpr hle
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (effectPhase p z w)]

end MathlibAnnex.CStarBilinear.Analytic
