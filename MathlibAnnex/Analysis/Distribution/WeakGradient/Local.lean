import MathlibAnnex.Analysis.Distribution.WeakGradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Interior compact localization and mollification. Arbitrary directions replace
coordinate basis vectors, so the proof works in any finite-dimensional real
normed space with a specified additive Haar measure.  The parent RET2 source
was independently elaborated; this API-repair revision is qualified by the exact build evidence accompanying this source. -/
noncomputable section
open Set Metric MeasureTheory Filter TopologicalSpace ContinuousLinearMap
open scoped ENNReal Topology Convolution BigOperators
namespace MathlibAnnex.WeakGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A quantitative ball contained in an open set. -/
structure LocalBallData (U : Set E) (x : E) where
  radius : ℝ
  radius_pos : 0 < radius
  closed_four_subset : closedBall x (4 * radius) ⊆ U

namespace LocalBallData

variable {U : Set E} {x : E}

/-- Inner open ball on which local constancy will be proved. -/
def inner (D : LocalBallData U x) : Set E := ball x D.radius

/-- Compact carrier used to localize the merely locally integrable function. -/
def carrier (D : LocalBallData U x) : Set E := closedBall x (4 * D.radius)

/-- Intermediate carrier containing every translated mollifier used above the
inner ball. -/
def middle (D : LocalBallData U x) : Set E := closedBall x (2 * D.radius)

@[simp] theorem center_mem_inner (D : LocalBallData U x) : x ∈ D.inner := by
  exact mem_ball_self D.radius_pos

 theorem inner_isOpen (D : LocalBallData U x) : IsOpen D.inner := isOpen_ball

 theorem inner_nonempty (D : LocalBallData U x) : D.inner.Nonempty :=
  ⟨x, D.center_mem_inner⟩

 theorem carrier_isCompact (D : LocalBallData U x) : IsCompact D.carrier :=
  isCompact_closedBall _ _

 theorem carrier_measurable (D : LocalBallData U x) : MeasurableSet D.carrier :=
  measurableSet_closedBall

 theorem carrier_subset (D : LocalBallData U x) : D.carrier ⊆ U :=
  D.closed_four_subset

 theorem inner_subset_carrier (D : LocalBallData U x) : D.inner ⊆ D.carrier := by
  intro y hy
  change dist y x < D.radius at hy
  exact mem_closedBall.mpr
    (hy.le.trans (by nlinarith [D.radius_pos]))

/-- A translated support of radius at most `D.radius` above an inner-ball point
is contained in the intermediate closed ball. -/
theorem translated_closedBall_subset_middle (D : LocalBallData U x)
    {y : E} (hy : y ∈ D.inner) {ρ : ℝ} (_hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ D.radius) : closedBall y ρ ⊆ D.middle := by
  change dist y x < D.radius at hy
  intro z hz
  have hzy : dist z y ≤ ρ := mem_closedBall.mp hz
  have hyx : dist y x < D.radius := hy
  have hzx : dist z x < 2 * D.radius := by
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < ρ + D.radius := add_lt_add_of_le_of_lt hzy hyx
      _ ≤ 2 * D.radius := by nlinarith
  exact mem_closedBall.mpr hzx.le

 theorem middle_subset_carrier (D : LocalBallData U x) : D.middle ⊆ D.carrier := by
  intro y hy
  have h : dist y x ≤ 2 * D.radius := mem_closedBall.mp hy
  exact mem_closedBall.mpr (h.trans (by nlinarith [D.radius_pos]))

 theorem middle_subset_open (D : LocalBallData U x) : D.middle ⊆ U :=
  D.middle_subset_carrier.trans D.carrier_subset

end LocalBallData

/-- Every point of an open set has a quantitative local ball. -/
theorem exists_localBallData {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    Nonempty (LocalBallData U x) := by

  rcases Metric.isOpen_iff.1 hU x hx with ⟨r, hr, hrU⟩
  let ρ := r / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨{ radius := ρ, radius_pos := hρ, closed_four_subset := ?_ }⟩
  intro y hy
  apply hrU
  have hyx : dist y x ≤ 4 * ρ := mem_closedBall.mp hy
  have : 4 * ρ < r := by dsimp [ρ]; nlinarith
  exact mem_ball.mpr (hyx.trans_lt this)

/-- Zero extension of `u` from a measurable compact carrier. -/
def compactLocalization (K : Set E)
    (u : E → ℝ) : E → ℝ := K.indicator u

@[simp] theorem compactLocalization_of_mem
    {K : Set E} {u : E → ℝ} {x : E} (hx : x ∈ K) :
    compactLocalization K u x = u x := by simp [compactLocalization, hx]

@[simp] theorem compactLocalization_of_not_mem
    {K : Set E} {u : E → ℝ} {x : E} (hx : x ∉ K) :
    compactLocalization K u x = 0 := by simp [compactLocalization, hx]

/-- Local integrability on `U` gives integrability on a compact subset of `U`. -/
theorem integrableOn_localBallCarrier {U : Set E}
    {u : E → ℝ} (hu : LocallyIntegrableOn u U μ)
    {x : E} (D : LocalBallData U x) :
    IntegrableOn u D.carrier μ := by
  exact hu.integrableOn_compact_subset D.carrier_subset D.carrier_isCompact

/-- The compact localization is globally integrable. -/
theorem compactLocalization_integrable {U : Set E}
    {u : E → ℝ} (hu : LocallyIntegrableOn u U μ)
    {x : E} (D : LocalBallData U x) :
    Integrable (compactLocalization D.carrier u) μ := by

  rw [compactLocalization, integrable_indicator_iff D.carrier_measurable]
  exact integrableOn_localBallCarrier hu D

/-- Hence the compact localization is globally locally integrable. -/
theorem compactLocalization_locallyIntegrable {U : Set E}
    {u : E → ℝ} (hu : LocallyIntegrableOn u U μ)
    {x : E} (D : LocalBallData U x) :
    LocallyIntegrable (compactLocalization D.carrier u) μ :=
  (compactLocalization_integrable hu D).locallyIntegrable

/-- On the inner ball, compact localization does not change the function. -/
theorem compactLocalization_eq_ae_inner {U : Set E}
    {u : E → ℝ} {x : E} (D : LocalBallData U x) :
    compactLocalization D.carrier u =ᵐ[μ.restrict D.inner] u := by
  filter_upwards [ae_restrict_mem (D.inner_isOpen.measurableSet)] with y hy
  exact compactLocalization_of_mem (D.inner_subset_carrier hy)


/-- Smooth bump centered at zero with explicit shrinking radii. -/
noncomputable def shrinkingBump (R : ℝ) (hR : 0 < R)
    (k : ℕ) : ContDiffBump (0 : E) where
  rIn := R / (2 * ((k + 2 : ℕ) : ℝ))
  rOut := R / (((k + 2 : ℕ) : ℝ))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hk : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) hk) hk).2
    nlinarith [hR]

@[simp] theorem shrinkingBump_rIn (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (shrinkingBump (E := E) R hR k).rIn =
      R / (2 * ((k + 2 : ℕ) : ℝ)) := rfl

@[simp] theorem shrinkingBump_rOut (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (shrinkingBump (E := E) R hR k).rOut =
      R / (((k + 2 : ℕ) : ℝ)) := rfl

/-- Uniform ratio required by the differentiation theorem. -/
theorem shrinkingBump_ratio (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (shrinkingBump (E := E) R hR k).rOut ≤
      2 * (shrinkingBump (E := E) R hR k).rIn := by
  rw [shrinkingBump_rOut, shrinkingBump_rIn]
  have hk : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply le_of_eq
  field_simp [hk]

/-- All outer radii are at most half of `R`. -/
theorem shrinkingBump_rOut_le_half (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (shrinkingBump (E := E) R hR k).rOut ≤ R / 2 := by
  have hk : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by norm_num
  exact div_le_div_of_nonneg_left hR.le (by positivity) hk

/-- Outer radii tend to zero. -/
theorem shrinkingBump_rOut_tendsto_zero (R : ℝ) (hR : 0 < R) :
    Tendsto (fun k : ℕ => (shrinkingBump (E := E) R hR k).rOut)
      atTop (𝓝 0) := by

  have hnat : Tendsto (fun k : ℕ => k + 2) atTop atTop := by
    exact tendsto_add_atTop_nat 2
  have hcast :
      Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_iff).2 hnat
  have hinv : Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcast
  simpa [shrinkingBump, div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv)

/-- The normalized mollification of a scalar function. -/
noncomputable def localMollification (R : ℝ) (hR : 0 < R)
    (v : E → ℝ) (k : ℕ) : E → ℝ :=
  (shrinkingBump (E := E) R hR k).normed μ ⋆[lsmul ℝ ℝ, μ] v

/-- The controlled mollifications converge a.e. to every globally locally
integrable scalar function. -/
theorem localMollification_tendsto_ae (R : ℝ) (hR : 0 < R)
    {v : E → ℝ} (hv : LocallyIntegrable v μ) :
    ∀ᵐ y ∂μ,
      Tendsto (fun k : ℕ => localMollification (μ := μ) R hR v k y)
        atTop (𝓝 (v y)) := by

  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (shrinkingBump_rOut_tendsto_zero (E := E) R hR)
    (Eventually.of_forall fun k => shrinkingBump_ratio (E := E) R hR k)
    hv

/-- Scalar normalized bump used in the `k`-th local mollification. -/
noncomputable def normalizedShrinkingBump (R : ℝ) (hR : 0 < R)
    (k : ℕ) : E → ℝ :=
  (shrinkingBump (E := E) R hR k).normed μ

/-- Translated bump field in direction `e`. -/
noncomputable def translatedBumpField (R : ℝ) (hR : 0 < R)
    (k : ℕ) (y : E) (e : E) : CompactC1VectorField E :=
  CompactC1VectorField.ofSupport
    (fun z => normalizedShrinkingBump (μ := μ) R hR k (y - z) • e)
    (closedBall y (shrinkingBump (E := E) R hR k).rOut)
    (isCompact_closedBall _ _)
    (by
      intro z hz
      have hφ : normalizedShrinkingBump (μ := μ) R hR k (y - z) ≠ 0 := by
        intro hzero
        exact hz (by simp [hzero])
      have hsupp : y - z ∈ Function.support
          (normalizedShrinkingBump (μ := μ) R hR k) := hφ
      have hball : y - z ∈ ball (0 : E)
          (shrinkingBump (E := E) R hR k).rOut := by

        simpa [normalizedShrinkingBump,
          ContDiffBump.support_normed_eq] using hsupp
      have : dist z y < (shrinkingBump (E := E) R hR k).rOut := by
        simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hball
      exact mem_closedBall.mpr this.le
    )
    (by

      exact (((shrinkingBump (E := E) R hR k).contDiff_normed
        (μ := μ) (n := (1 : ℕ∞))).comp
        (contDiff_const.sub contDiff_id)).smul contDiff_const)


/-- The translated field is supported inside `U` above an inner-ball point. -/
theorem translatedBumpField_carrier_subset
    {U : Set E} {x : E} (D : LocalBallData U x)
    {y : E} (hy : y ∈ D.inner) (k : ℕ) (e : E) :
    (translatedBumpField (μ := μ) D.radius D.radius_pos k y e).carrier ⊆ U := by
  intro z hz
  exact D.middle_subset_open
    (D.translated_closedBall_subset_middle hy
      (le_of_lt (shrinkingBump (E := E) D.radius D.radius_pos k).rOut_pos)
      ((shrinkingBump_rOut_le_half (E := E) D.radius D.radius_pos k).trans
        (by nlinarith [D.radius_pos])) hz)


/-- The translated field tests an arbitrary direction, not a selected basis. -/
theorem divergence_translatedBumpField
    (R : ℝ) (hR : 0 < R) (k : ℕ) (y z : E) (e : E) :
    divergence (translatedBumpField (μ := μ) R hR k y e) z =
      - fderiv ℝ (normalizedShrinkingBump (μ := μ) R hR k) (y - z) e := by
  apply divergence_sub_smul
  exact ((shrinkingBump (E := E) R hR k).contDiff_normed
    (μ := μ) (n := (1 : ℕ∞))).differentiable (by norm_num) (y - z)

/-- Derivative of the mollification in one direction, written with
the same translated kernel as the weak test field. -/
theorem localMollification_fderiv_apply
    (R : ℝ) (hR : 0 < R) {v : E → ℝ}
    (hv : LocallyIntegrable v μ) (k : ℕ) (y : E) (e : E) :
    fderiv ℝ (localMollification (μ := μ) R hR v k) y (e) =
      ∫ z, v z *
        fderiv ℝ (normalizedShrinkingBump (μ := μ) R hR k) (y - z) (e) ∂μ := by

  -- `HasCompactSupport.hasFDerivAt_convolution_left` differentiates the bump.
  -- The provider's Haar change-of-variable lemma rewrites the
  -- derivative convolution in the displayed `y-z` form.
  have hφc : HasCompactSupport
      (normalizedShrinkingBump (μ := μ) (E := E) R hR k) := by
    exact (shrinkingBump (E := E) R hR k).hasCompactSupport_normed
  have hφd : ContDiff ℝ 1
      (normalizedShrinkingBump (μ := μ) (E := E) R hR k) :=
    (shrinkingBump (E := E) R hR k).contDiff_normed
      (μ := μ) (n := (1 : ℕ∞))
  have hderiv := hφc.hasFDerivAt_convolution_left
    (lsmul ℝ ℝ) hφd hv y
  have hbase :=
    congrArg (fun L : E →L[ℝ] ℝ => L (e)) hderiv.fderiv
  change (fderiv ℝ
      ((normalizedShrinkingBump (μ := μ) (E := E) R hR k) ⋆[lsmul ℝ ℝ, μ] v) y)
      (e) = _
  rw [hbase]
  have hint := ((hφc.fderiv ℝ).convolutionExists_left
      (ContinuousLinearMap.precompL E (lsmul ℝ ℝ))
      (hφd.continuous_fderiv one_ne_zero) hv) y
  change Integrable (fun t : E =>
      (ContinuousLinearMap.precompL E (lsmul ℝ ℝ)
        (fderiv ℝ (normalizedShrinkingBump (μ := μ) (E := E) R hR k) t))
        (v (y - t))) μ at hint
  rw [MeasureTheory.convolution_def]
  rw [ContinuousLinearMap.integral_apply hint (e)]
  have hcv := (Measure.measurePreserving_sub_left μ y).integral_comp
    (MeasurableEquiv.subLeft y).measurableEmbedding
    (fun z : E => v z *
      fderiv ℝ (normalizedShrinkingBump (μ := μ) (E := E) R hR k)
        (y - z) (e))
  simpa [localMollification, normalizedShrinkingBump,
    ContinuousLinearMap.precompL_apply, MeasureTheory.convolution_def,
    sub_sub_cancel, mul_comm] using hcv


/-- The weak integral over `U` equals the corresponding whole-space integral
with the compact localization. -/
theorem weakIntegral_eq_localized_bumpIntegral
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x)
    {y : E} (hy : y ∈ D.inner) (k : ℕ) (e : E) :
    ∫ z, compactLocalization D.carrier u z *
        divergence (translatedBumpField (μ := μ) D.radius D.radius_pos k y e) z ∂μ = 0 := by
  let W := translatedBumpField (μ := μ) D.radius D.radius_pos k y e
  have hWU : W.carrier ⊆ U :=
    translatedBumpField_carrier_subset D hy k e
  have hzero := hweak W hWU
  have hsupport : ∀ᵐ z ∂μ,
      compactLocalization D.carrier u z * divergence W z =
        (U.indicator fun z => u z * divergence W z) z := by
    filter_upwards with z
    by_cases hzW : z ∈ W.carrier
    · have hzK : z ∈ D.carrier := by
        exact D.middle_subset_carrier
          (D.translated_closedBall_subset_middle hy
            (le_of_lt (shrinkingBump (E := E) D.radius D.radius_pos k).rOut_pos)
            ((shrinkingBump_rOut_le_half (E := E) D.radius D.radius_pos k).trans
              (by nlinarith [D.radius_pos])) hzW)
      have hzU : z ∈ U := hWU hzW
      simp [compactLocalization, hzK, hzU]
    · have hdiv : divergence W z = 0 := by

        -- Closedness of the compact carrier gives a zero neighborhood.
        have hfd := W.fderiv_eq_zero_of_not_mem_carrier hzW
        simp [divergence, hfd]
      rw [hdiv]
      by_cases hzU : z ∈ U <;> simp [hzU, hdiv]
  rw [integral_congr_ae hsupport]
  simpa [MeasureTheory.integral_indicator hU.measurableSet] using hzero

/-- Every directional derivative of the local mollification vanishes on the
inner ball. -/
theorem localMollification_fderiv_apply_eq_zero
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x)
    {y : E} (hy : y ∈ D.inner) (k : ℕ) (e : E) :
    fderiv ℝ
      (localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k) y (e) = 0 := by
  rw [localMollification_fderiv_apply D.radius D.radius_pos
    (compactLocalization_locallyIntegrable hu D) k y e]
  have hweak0 := weakIntegral_eq_localized_bumpIntegral hU hweak D hy k e
  simp_rw [divergence_translatedBumpField] at hweak0
  have hneg : -(∫ z, compactLocalization D.carrier u z *
      fderiv ℝ (normalizedShrinkingBump (μ := μ) D.radius D.radius_pos k)
        (y - z) (e) ∂μ) = 0 := by
    simpa only [mul_neg, integral_neg] using hweak0
  exact neg_eq_zero.mp hneg

/-- Vanishing in every direction is vanishing of the full derivative. -/
theorem localMollification_fderiv_eq_zero
    {U : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U μ) (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x) (k : ℕ) :
    Set.EqOn (fderiv ℝ (localMollification (μ := μ) D.radius D.radius_pos
      (compactLocalization D.carrier u) k)) 0 D.inner := by
  intro y hy
  apply ContinuousLinearMap.ext
  intro e
  exact localMollification_fderiv_apply_eq_zero hU hu hweak D hy k e

/-- The local mollification is smooth. -/
theorem localMollification_contDiff
    {U : Set E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    {x : E} (D : LocalBallData U x) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k) := by

  exact (shrinkingBump (E := E) D.radius D.radius_pos k).hasCompactSupport_normed
    |>.contDiff_convolution_left (lsmul ℝ ℝ)
      ((shrinkingBump (E := E) D.radius D.radius_pos k).contDiff_normed
        (μ := μ) (n := (⊤ : ℕ∞)))
      (compactLocalization_locallyIntegrable hu D)

/-- Each mollification is pointwise constant on the connected inner ball. -/
theorem exists_localMollification_constant
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x) (k : ℕ) :
    ∃ c : ℝ, ∀ y ∈ D.inner,
      localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k y = c := by
  have hsmooth := localMollification_contDiff hu D k
  exact D.inner_isOpen.exists_is_const_of_fderiv_eq_zero
    (convex_ball x D.radius |>.isPreconnected)
    (hsmooth.differentiable (by simp)).differentiableOn
    (localMollification_fderiv_eq_zero hU hu hweak D k)


/-- Inner balls have positive Haar measure. -/
theorem localBall_inner_measure_pos {U : Set E}
    {x : E} (D : LocalBallData U x) : 0 < μ D.inner := by
  exact D.inner_isOpen.measure_pos μ D.inner_nonempty

/-- There is a convergence point of the mollifier sequence inside the inner
ball. -/
theorem exists_inner_convergencePoint {U : Set E}
    {u : E → ℝ} (hu : LocallyIntegrableOn u U μ)
    {x : E} (D : LocalBallData U x) :
    ∃ y₀ ∈ D.inner,
      Tendsto
        (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
          (compactLocalization D.carrier u) k y₀)
        atTop (𝓝 (compactLocalization D.carrier u y₀)) := by
  have hconv := localMollification_tendsto_ae D.radius D.radius_pos
    (compactLocalization_locallyIntegrable hu D)
  have hconvInner : ∀ᵐ y ∂μ.restrict D.inner,
      Tendsto
        (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
          (compactLocalization D.carrier u) k y)
        atTop (𝓝 (compactLocalization D.carrier u y)) :=
    ae_restrict_of_ae hconv
  have hmem : ∀ᵐ y ∂μ.restrict D.inner, y ∈ D.inner :=
    ae_restrict_mem D.inner_isOpen.measurableSet
  have hpos := localBall_inner_measure_pos (μ := μ) D
  haveI : (ae (μ.restrict D.inner)).NeBot :=
    MeasureTheory.ae_restrict_neBot.mpr hpos.ne'

  -- Select a common convergence point in the positive-measure ball.
  obtain ⟨y₀, hcy, hy₀⟩ :=
    (hconvInner.and hmem).exists
  exact ⟨y₀, hy₀, hcy⟩

/-- Equality of every mollified value on the inner ball. -/
theorem localMollification_eq_at_inner_points
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x)
    {y z : E} (hy : y ∈ D.inner) (hz : z ∈ D.inner) (k : ℕ) :
    localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k y =
      localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k z := by
  rcases exists_localMollification_constant hU hu hweak D k with ⟨c, hc⟩
  exact (hc y hy).trans (hc z hz).symm

/-- The compact localization is a.e. constant on the inner ball. -/
theorem compactLocalization_aeConstant_inner
    {U : Set E} (hU : IsOpen U)
    {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x) :
    ∃ c : ℝ, AEConstantOn μ
      (compactLocalization D.carrier u) D.inner c := by
  rcases exists_inner_convergencePoint hu D with ⟨y₀, hy₀, hconv₀⟩
  refine ⟨compactLocalization D.carrier u y₀, ?_⟩
  have hconv := localMollification_tendsto_ae D.radius D.radius_pos
    (compactLocalization_locallyIntegrable hu D)
  have hconvInner : ∀ᵐ y ∂μ.restrict D.inner,
      Tendsto
        (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
          (compactLocalization D.carrier u) k y)
        atTop (𝓝 (compactLocalization D.carrier u y)) :=
    ae_restrict_of_ae hconv
  filter_upwards [hconvInner,
    ae_restrict_mem D.inner_isOpen.measurableSet] with y hconvy hy
  have heq :
      (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k y) =
      (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k y₀) := by
    funext k
    exact localMollification_eq_at_inner_points hU hu hweak D hy hy₀ k
  have hconv₀' : Tendsto
      (fun k : ℕ => localMollification (μ := μ) D.radius D.radius_pos
        (compactLocalization D.carrier u) k y)
      atTop (𝓝 (compactLocalization D.carrier u y₀)) := by
    simpa [heq] using hconv₀
  exact tendsto_nhds_unique hconvy hconv₀' 

/-- The original function is a.e. constant on the same inner ball. -/
theorem exists_aeConstant_inner
    {U : Set E} (hU : IsOpen U)
    {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (D : LocalBallData U x) :
    ∃ c : ℝ, AEConstantOn μ u D.inner c := by
  rcases compactLocalization_aeConstant_inner hU hu hweak D with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact (compactLocalization_eq_ae_inner D).symm.trans hc

/-- Every point has an open neighborhood on which the function is a.e.
constant. -/
theorem exists_localAEConstantAt
    {U : Set E} (hU : IsOpen U)
    {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    (hweak : WeakDivergenceZero μ U u)
    {x : E} (hx : x ∈ U) :
    Nonempty (LocalAEConstantAt μ U u x) := by
  rcases exists_localBallData hU hx with ⟨D⟩
  rcases exists_aeConstant_inner hU hu hweak D with ⟨c, hc⟩
  refine ⟨{
    neighborhood := D.inner
    neighborhood_open := D.inner_isOpen
    mem_neighborhood := D.center_mem_inner
    neighborhood_subset := D.inner_subset_carrier.trans D.carrier_subset
    constant := c
    ae_eq := hc }⟩


end MathlibAnnex.WeakGradient
