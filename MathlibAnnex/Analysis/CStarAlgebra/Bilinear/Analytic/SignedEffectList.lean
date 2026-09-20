import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.NormalizedEffects

/-!
# Finite signed sums of effects and their analytic cost

Lists are used only as a concrete finite indexing device.  They allow repeated
and zero coefficients and impose no dimension or cardinality bound.  The
estimate is derived from the proved two-effect bound.  SOURCE_UNBUILT.
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

/-- Concrete value of a finite signed effect sum. -/
def effectValue : List (ℝ × A) → A
  | [] => 0
  | (c, p) :: L => c • p + effectValue L

/-- Marginal square-root cost of a finite signed effect sum. -/
def effectCost (phi : A →L[ℂ] ℂ) : List (ℝ × A) → ℝ
  | [] => 0
  | (c, p) :: L => |c| * Real.sqrt (phi p).re + effectCost phi L

/-- Each algebra element in the list is an effect; coefficients are arbitrary
real numbers and are not assumed positive. -/
def HasEffects (L : List (ℝ × A)) : Prop :=
  ∀ cp ∈ L, 0 ≤ cp.2 ∧ cp.2 ≤ 1

theorem effectCost_nonneg (phi : A →L[ℂ] ℂ) (L : List (ℝ × A)) :
    0 ≤ effectCost phi L := by
  induction L with
  | nil => simp [effectCost]
  | cons cp L ih =>
      exact add_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) ih

theorem effectValue_append (L M : List (ℝ × A)) :
    effectValue (L ++ M) = effectValue L + effectValue M := by
  induction L with
  | nil => simp [effectValue]
  | cons cp L ih => simp [effectValue, ih, add_assoc]

theorem effectCost_append (phi : A →L[ℂ] ℂ) (L M : List (ℝ × A)) :
    effectCost phi (L ++ M) = effectCost phi L + effectCost phi M := by
  induction L with
  | nil => simp [effectCost]
  | cons cp L ih => simp [effectCost, ih, add_assoc]

/-- Negation changes coefficients, not positive effects. -/
def negateCoefficients (L : List (ℝ × A)) : List (ℝ × A) :=
  L.map (fun cp ↦ (-cp.1, cp.2))

theorem effectValue_negateCoefficients (L : List (ℝ × A)) :
    effectValue (negateCoefficients L) = -effectValue L := by
  induction L with
  | nil => simp [negateCoefficients, effectValue]
  | cons cp L ih =>
      change (-cp.1) • cp.2 + effectValue (negateCoefficients L) =
        -(cp.1 • cp.2 + effectValue L)
      rw [neg_smul, ih]
      abel

theorem effectCost_negateCoefficients (phi : A →L[ℂ] ℂ) (L : List (ℝ × A)) :
    effectCost phi (negateCoefficients L) = effectCost phi L := by
  induction L with
  | nil => simp [negateCoefficients, effectCost]
  | cons cp L ih =>
      simpa only [negateCoefficients, List.map_cons, effectCost, abs_neg] using
        congrArg (fun r ↦ |cp.1| * Real.sqrt (phi cp.2).re + r) ih

theorem hasEffects_negateCoefficients {L : List (ℝ × A)} (hL : HasEffects L) :
    HasEffects (negateCoefficients L) := by
  intro cp hcp
  obtain ⟨dq, hdq, rfl⟩ := List.mem_map.mp hcp
  exact hL dq hdq

/-- The imaginary part respects real scalar multiplication exactly. -/
theorem im_apply_real_smul_left (V : A →L[ℂ] D →L[ℂ] ℂ)
    (c : ℝ) (a : A) (d : D) :
    (V (c • a) d).im = c * (V a d).im := by
  rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp [smul_eq_mul, Complex.mul_im]

theorem im_apply_real_smul_right (V : A →L[ℂ] D →L[ℂ] ℂ)
    (c : ℝ) (a : A) (d : D) :
    (V a (c • d)).im = c * (V a d).im := by
  rw [ContinuousLinearMap.map_smul_of_tower]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp [smul_eq_mul, Complex.mul_im]

/-- One effect against a whole signed finite sum. -/
theorem normalized_abs_im_effect_list_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (p : A) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (M : List (ℝ × D)) (hM : HasEffects M) :
    |(V p (effectValue M)).im| ≤
      Real.sqrt (V p 1).re * effectCost (rightMarginal V) M := by
  induction M with
  | nil => simp [effectValue, effectCost]
  | cons dq M ih =>
      have hq := hM dq (by simp)
      have htail : HasEffects M := fun cp hcp ↦ hM cp (by simp [hcp])
      have hi := ih htail
      have he := normalized_abs_im_effect_le V hV h1 p hp hp1 dq.2 hq.1 hq.2
      change |(V p (dq.1 • dq.2 + effectValue M)).im| ≤ _
      rw [map_add, Complex.add_im, im_apply_real_smul_right]
      calc
        _ ≤ |dq.1 * (V p dq.2).im| + |(V p (effectValue M)).im| := abs_add_le _ _
        _ = |dq.1| * |(V p dq.2).im| + |(V p (effectValue M)).im| := by rw [abs_mul]
        _ ≤ |dq.1| * (Real.sqrt (V p 1).re * Real.sqrt (V 1 dq.2).re) +
            Real.sqrt (V p 1).re * effectCost (rightMarginal V) M := by
          gcongr
        _ = _ := by simp only [effectCost, rightMarginal_apply]; ring

/-- Two arbitrary signed finite effect sums.  All positivity and analytic
inputs come from the normalized bilinear form, rather than a supplied
finite-family inequality. -/
theorem normalized_abs_im_lists_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (L : List (ℝ × A)) (hL : HasEffects L)
    (M : List (ℝ × D)) (hM : HasEffects M) :
    |(V (effectValue L) (effectValue M)).im| ≤
      effectCost (leftMarginal V) L * effectCost (rightMarginal V) M := by
  induction L with
  | nil => simp [effectValue, effectCost]
  | cons cp L ih =>
      have hp := hL cp (by simp)
      have htail : HasEffects L := fun dq hdq ↦ hL dq (by simp [hdq])
      have hi := ih htail
      have he := normalized_abs_im_effect_list_le V hV h1 cp.2 hp.1 hp.2 M hM
      change |(V (cp.1 • cp.2 + effectValue L) (effectValue M)).im| ≤ _
      rw [map_add, ContinuousLinearMap.add_apply, Complex.add_im,
        im_apply_real_smul_left]
      calc
        _ ≤ |cp.1 * (V cp.2 (effectValue M)).im| +
            |(V (effectValue L) (effectValue M)).im| := abs_add_le _ _
        _ = |cp.1| * |(V cp.2 (effectValue M)).im| +
            |(V (effectValue L) (effectValue M)).im| := by rw [abs_mul]
        _ ≤ |cp.1| * (Real.sqrt (V cp.2 1).re * effectCost (rightMarginal V) M) +
            effectCost (leftMarginal V) L * effectCost (rightMarginal V) M := by
          gcongr
        _ = _ := by simp only [effectCost, leftMarginal_apply]; ring

end MathlibAnnex.CStarBilinear.Analytic
