import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.EffectPhase
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic

/-!
# The normalized analytic estimate on effects

For an arbitrary bounded bilinear form of norm at most one with V(1,1)=1,
this file derives positive marginals and the imaginary covariance estimate
on every pair of positive contractions.  The estimate is proved, not passed
as a factorization, weak-compactness, or extension hypothesis.
SOURCE_UNBUILT; existing order instances are retained.
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

/-- The marginal obtained by fixing the second argument at the identity. -/
def leftMarginal (V : A →L[ℂ] D →L[ℂ] ℂ) : A →L[ℂ] ℂ := V.flip 1

/-- The marginal obtained by fixing the first argument at the identity. -/
def rightMarginal (V : A →L[ℂ] D →L[ℂ] ℂ) : D →L[ℂ] ℂ := V 1

@[simp] theorem leftMarginal_apply (V : A →L[ℂ] D →L[ℂ] ℂ) (a : A) :
    leftMarginal V a = V a 1 := rfl

@[simp] theorem rightMarginal_apply (V : A →L[ℂ] D →L[ℂ] ℂ) (d : D) :
    rightMarginal V d = V 1 d := rfl

/-- Normalized marginals are actual states, by the existing norm-one
functional positivity theorem. -/
theorem normalized_marginals_are_states (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1) :
    leftMarginal V ∈ stateSpace A ∧ rightMarginal V ∈ stateSpace D := by
  have hleft : ‖leftMarginal V‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro a
    change ‖V a 1‖ ≤ 1 * ‖a‖
    calc
      ‖V a 1‖ ≤ ‖V a‖ * ‖(1 : D)‖ := (V a).le_opNorm 1
      _ = ‖V a‖ := by simp
      _ ≤ ‖V‖ * ‖a‖ := V.le_opNorm a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hV (norm_nonneg _)
  have hright : ‖rightMarginal V‖ ≤ 1 := by
    calc
      ‖rightMarginal V‖ = ‖V 1‖ := rfl
      _ ≤ ‖V‖ * ‖(1 : A)‖ := V.le_opNorm 1
      _ ≤ 1 := by simpa using hV
  exact ⟨⟨nonnegative_of_norm_le_one_of_apply_one _ hleft h1, h1⟩,
    ⟨nonnegative_of_norm_le_one_of_apply_one _ hright h1, h1⟩⟩

/-- Real scalar coordinates of a state on an effect, with both endpoints
included. -/
theorem state_effect_coordinates (phi : A →L[ℂ] ℂ)
    (hphi : phi ∈ stateSpace A) (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (phi p).re ∧ (phi p).re ≤ 1 ∧ phi p = ((phi p).re : ℂ) := by
  have hpos := RCLike.nonneg_iff.mp (hphi.1 p hp)
  have hcomp := RCLike.nonneg_iff.mp (hphi.1 (1 - p) (sub_nonneg.mpr hp1))
  have hval : phi (1 - p) = 1 - phi p := by rw [map_sub, hphi.2]
  refine ⟨hpos.1, ?_, ?_⟩
  · rw [hval] at hcomp
    have hcre := hcomp.1
    change 0 ≤ 1 - (phi p).re at hcre
    linarith
  · apply Complex.ext
    · simp
    · simpa using hpos.2

/-- Contractivity applied to two contractions, with the same bounded bilinear
operator norm as in the original problem. -/
theorem normalized_value_norm_le_one (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (x : A) (y : D) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖V x y‖ ≤ 1 := by
  calc
    ‖V x y‖ ≤ ‖V x‖ * ‖y‖ := (V x).le_opNorm y
    _ ≤ (‖V‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (V.le_opNorm x) (norm_nonneg _)
    _ ≤ (1 * 1) * 1 := by gcongr
    _ = 1 := by norm_num

/-- The test value reduces to a scalar polynomial using only bilinearity,
normalization, the two real marginals and scalar unit identities. -/
theorem bilinear_effectPhase_value (V : A →L[ℂ] D →L[ℂ] ℂ)
    (h1 : V 1 1 = 1) (p : A) (q : D) (s t : ℝ)
    (hs : V p 1 = (s : ℂ)) (ht : V 1 q = (t : ℂ))
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    V (effectPhase p z w) (effectPhase q 1 (star (z * w))) =
      phasePolynomial (V p q) s t z w := by
  have hzs : z * star z = 1 := by
    rw [mul_comm]
    exact star_mul_unit_scalar z hz
  have hws : w * star w = 1 := by
    rw [mul_comm]
    exact star_mul_unit_scalar w hw
  have hzc : z * star (z * w) = star w := by
    rw [star_mul]
    calc
      z * (star w * star z) = (z * star z) * star w := by ring
      _ = star w := by rw [hzs, one_mul]
  have hwc : w * star (z * w) = star z := by
    rw [star_mul]
    calc
      w * (star w * star z) = (w * star w) * star z := by ring
      _ = star z := by rw [hws, one_mul]
  calc
    _ = z * V p q + (z * star (z * w)) * ((s : ℂ) - V p q) +
        w * ((t : ℂ) - V p q) +
        (w * star (z * w)) * (1 - (s : ℂ) - (t : ℂ) + V p q) := by
      simp only [effectPhase, one_smul, map_add, map_sub, map_smul,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, h1, hs, ht]
      ring
    _ = _ := by rw [hzc, hwc]; rfl

/-- The essential two-effect estimate.  It is not restricted to projections.
All marginal zero/one cases follow from the same scalar ellipse proof. -/
theorem normalized_im_effect_sq_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (q : D) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (V p q).im ^ 2 ≤
      (V p 1).re * (1 - (V p 1).re) *
        (V 1 q).re * (1 - (V 1 q).re) := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  have hsp := (state_effect_coordinates (leftMarginal V) hphi p hp hp1).2.2
  have htq := (state_effect_coordinates (rightMarginal V) hpsi q hq hq1).2.2
  have hsp' : V p 1 = (((V p 1).re : ℂ)) := by
    simpa only [leftMarginal_apply] using hsp
  have htq' : V 1 q = (((V 1 q).re : ℂ)) := by
    simpa only [rightMarginal_apply] using htq
  apply covariance_of_phasePolynomial_bound (V p q) (V p 1).re (V 1 q).re
  intro z w hz hw
  rw [← bilinear_effectPhase_value V h1 p q _ _ hsp' htq' z w hz hw]
  exact normalized_value_norm_le_one V hV _ _
    (norm_effectPhase_le_one p hp hp1 z w hz hw)
    (norm_effectPhase_le_one q hq hq1 1 (star (z * w)) (by simp)
      (by simp [norm_mul, hz, hw]))

/-- The weaker product estimate is convenient for finite continuous slices. -/
theorem normalized_abs_im_effect_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (q : D) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    |(V p q).im| ≤ Real.sqrt (V p 1).re * Real.sqrt (V 1 q).re := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  obtain ⟨hs0, hs1, _⟩ := state_effect_coordinates (leftMarginal V) hphi p hp hp1
  obtain ⟨ht0, ht1, _⟩ := state_effect_coordinates (rightMarginal V) hpsi q hq hq1
  change 0 ≤ (V p 1).re at hs0
  change (V p 1).re ≤ 1 at hs1
  change 0 ≤ (V 1 q).re at ht0
  change (V 1 q).re ≤ 1 at ht1
  have hs : (V p 1).re * (1 - (V p 1).re) ≤ (V p 1).re := by nlinarith
  have ht : (V 1 q).re * (1 - (V 1 q).re) ≤ (V 1 q).re := by nlinarith
  have hm := mul_le_mul hs ht (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hs0
  have hsq : (V p q).im ^ 2 ≤ (V p 1).re * (V 1 q).re := by
    have he := normalized_im_effect_sq_le V hV h1 p hp hp1 q hq hq1
    nlinarith [hm]
  have hrsq : (Real.sqrt (V p 1).re * Real.sqrt (V 1 q).re) ^ 2 =
      (V p 1).re * (V 1 q).re := by
    rw [mul_pow, Real.sq_sqrt hs0, Real.sq_sqrt ht0]
  nlinarith [sq_abs (V p q).im, abs_nonneg (V p q).im,
    mul_nonneg (Real.sqrt_nonneg (V p 1).re) (Real.sqrt_nonneg (V 1 q).re)]

end MathlibAnnex.CStarBilinear.Analytic
