import MathlibAnnex.Analysis.Normed.Sphere.RadialBall
import MathlibAnnex.MeasureTheory.Integral.MaximalMinor
import MathlibAnnex.Analysis.Calculus.BilipschitzOrientation
import MathlibAnnex.MeasureTheory.Measure.EquivalentSeminormBall
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Gauge

/-! # Absolute radial Jacobian integral
The derivative is taken in the reference finite Pi norm, with source `MX` and
target `MY`. The integral of the absolute determinant equals the target closed
unit ball's original Lebesgue volume. The public integral theorem retains the
source positive dimension `m + 1`; no signed integral is asserted.
Private model witnesses are reconstructed locally from the accepted providers.
-/

noncomputable section
open Set Metric Function MeasureTheory
open scoped NNReal ENNReal
namespace MathlibAnnex.Sphere
open EquivalentSeminorm

private abbrev radialMap {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  show Fin n → ℝ from radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x)

@[simp] private theorem radialMap_p {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x : Fin n → ℝ) :
    MY.p (radialMap Δ x) = MX.p x := radialExtension_norm Δ (show Space MX from x)

private theorem radialMap_leftInverse {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    LeftInverse (radialMap Δ.symm) (radialMap Δ) :=
  fun x => radialExtension_leftInverse Δ (show Space MX from x)

private theorem radialMap_model_dist {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x y : Fin n → ℝ) :
    MY.p (radialMap Δ x - radialMap Δ y) ≤ 3 * MX.p (x - y) := by
  have h := (radialExtension_lipschitz Δ).dist_le_mul
    (show Space MX from x) (show Space MX from y)
  simpa only [dist_space_eq, NNReal.coe_ofNat] using h

private theorem radialMap_lipschitz {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    LipschitzWith (3 * MX.upper / MY.lower).toNNReal (radialMap Δ) := by
  have hC : 0 ≤ 3 * MX.upper / MY.lower := div_nonneg (mul_nonneg (by norm_num) MX.upper_pos.le) MY.lower_pos.le
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hlower := MY.lower_le (radialMap Δ x - radialMap Δ y)
  have hmodel := radialMap_model_dist Δ x y
  have hupper := MX.le_upper (x - y)
  rw [Real.coe_toNNReal _ hC, dist_eq_norm, dist_eq_norm]
  calc
    ‖radialMap Δ x - radialMap Δ y‖ ≤ (3 * MX.upper * ‖x - y‖) / MY.lower :=
      (le_div_iff₀ MY.lower_pos).2 (by nlinarith)
    _ = (3 * MX.upper / MY.lower) * ‖x - y‖ := by ring

namespace Internal
private def referenceAntiConstant {n : ℕ} (MX MY : EquivalentSeminorm (Fin n → ℝ)) : ℝ :=
  MX.lower / (3 * MY.upper)

private theorem referenceAntiConstant_pos {n : ℕ} (MX MY : EquivalentSeminorm (Fin n → ℝ)) :
    0 < referenceAntiConstant MX MY :=
  div_pos MX.lower_pos (mul_pos (by norm_num) MY.upper_pos)
end Internal
open Internal

private theorem radialMap_lower {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x y : Fin n → ℝ) :
    referenceAntiConstant MX MY * ‖x - y‖ ≤ ‖radialMap Δ x - radialMap Δ y‖ := by
  have hinv := radialMap_model_dist Δ.symm (radialMap Δ x) (radialMap Δ y)
  rw [radialMap_leftInverse Δ x, radialMap_leftInverse Δ y] at hinv
  have hlow := MX.lower_le (x - y)
  have hup := MY.le_upper (radialMap Δ x - radialMap Δ y)
  have hden : 0 < 3 * MY.upper := mul_pos (by norm_num) MY.upper_pos
  have hprod : MX.lower * ‖x - y‖ ≤ (3 * MY.upper) *
      ‖radialMap Δ x - radialMap Δ y‖ := by nlinarith
  dsimp [referenceAntiConstant]
  calc
    MX.lower / (3 * MY.upper) * ‖x - y‖ =
      (MX.lower * ‖x - y‖) / (3 * MY.upper) := by ring
    _ ≤ ‖radialMap Δ x - radialMap Δ y‖ :=
      (div_le_iff₀ hden).2 (by simpa only [mul_comm] using hprod)

private theorem openBall_isOpen {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    IsOpen (M.p.ball 0 1) := by
  rw [Seminorm.ball_zero_eq]
  exact isOpen_lt M.continuous_p continuous_const

private theorem openBall_convex {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    Convex ℝ (M.p.ball 0 1) := M.p.convex_ball 0 1

private theorem openBall_connected {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    IsConnected (M.p.ball 0 1) := by
  refine (openBall_convex M).isConnected ?_
  exact ⟨0, by simp⟩

private theorem source_B52 {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (radialMap Δ) x :=
  (radialMap_lipschitz Δ).ae_differentiableAt

namespace Internal
private def radialGoodSet {n : ℕ} {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : (sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)) : Set ((Fin n → ℝ)) :=
  (MX.p.ball 0 1) ∩ {x | DifferentiableAt ℝ (radialMap Δ) x}
end Internal
open Internal
private theorem radial_badSet_null {n : ℕ} {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : (sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)) :
    volume ((MX.p.ball 0 1) \ radialGoodSet Δ) = 0 := by
  -- [R15-API-CHECK:SJ-AREA-001]
  have hC := radialMap_lipschitz Δ
  have hdiff : ∀ᵐ x ∂volume.restrict ((MX.p.ball 0 1)),
      DifferentiableAt ℝ (radialMap Δ) x :=
    ae_restrict_of_ae hC.ae_differentiableAt
  have hfull : ∀ᵐ x ∂volume,
      x ∈ (MX.p.ball 0 1) →
        DifferentiableAt ℝ (radialMap Δ) x :=
    (ae_restrict_iff' (openBall_isOpen MX).measurableSet).mp hdiff
  have hset : (MX.p.ball 0 1) \ radialGoodSet Δ =
      {x | ¬(x ∈ (MX.p.ball 0 1) →
        DifferentiableAt ℝ (radialMap Δ) x)} := by
    ext x
    simp [radialGoodSet]
  rw [hset]
  exact ae_iff.mp hfull

private theorem radial_image_badSet_null {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    volume (radialMap Δ '' (MX.p.ball 0 1 \ radialGoodSet Δ)) = 0 :=
  BilipschitzOrientation.volume_image_eq_zero_of_lipschitzWith
    (radialMap_lipschitz Δ) (radial_badSet_null Δ)

private theorem radial_abs_det_integrableOn {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    IntegrableOn (fun x => |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)|)
      MX.closedUnitBall volume := by
  let s := Matrix.MaximalMinorIndex.ofOrderEmbedding
    (OrderIso.refl (Fin (m + 1))).toOrderEmbedding
  have h := NullLagrangian.integrableOn_maximalMinor_fderiv_of_lipschitzWith
    s (radialMap_lipschitz Δ) MX.closedUnitBall_isCompact
  have hsel (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)) :
      ContinuousLinearMap.selectedSquare s A = A := by
    ext x i
    simp [ContinuousLinearMap.selectedSquare, s]
  have heq : NullLagrangian.maximalMinorIntegrand s (radialMap Δ) =
      (fun x => ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)) := by
    funext x
    unfold NullLagrangian.maximalMinorIntegrand
    rw [hsel]
  rw [heq] at h
  simpa only [IntegrableOn, Real.norm_eq_abs] using h.norm

private theorem radial_lintegral_abs_det_eq_openBall_volume {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)} (Δ : (sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)) :
    (∫⁻ x in (MX.p.ball 0 1),
      ENNReal.ofReal |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume) =
      volume ((MY.p.ball 0 1)) := by
  -- [R15-API-CHECK:SJ-AREA-003]
  let G := radialGoodSet Δ
  have hGmeas : MeasurableSet G := by
    exact (openBall_isOpen MX).measurableSet.inter
      (measurableSet_of_differentiableAt ℝ (radialMap Δ))
  have hder : ∀ x ∈ G,
      HasFDerivWithinAt (radialMap Δ)
        (fderiv ℝ (radialMap Δ) x) G x := by
    intro x hx
    exact hx.2.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (radialMap Δ) G :=
    (radialMap_leftInverse Δ).injective.injOn
  have harea := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    volume hGmeas hder hinj
  have hdomain :
      (∫⁻ x in (MX.p.ball 0 1),
        ENNReal.ofReal |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume) =
      ∫⁻ x in G,
        ENNReal.ofReal |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume := by
    apply setLIntegral_congr
    apply ae_eq_set.mpr
    constructor
    · simpa only [G] using radial_badSet_null Δ
    · have hempty : G \ (MX.p.ball 0 1) = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hx.2 hx.1.1).elim
        · intro hx
          exact hx.elim
      rw [hempty, measure_empty]
  have himage : volume (radialMap Δ '' G) =
      volume ((MY.p.ball 0 1)) := by
    rw [← radialExtension_image_ball Δ]
    have hsplit : radialMap Δ '' (MX.p.ball 0 1) =
        radialMap Δ '' G ∪
          radialMap Δ '' ((MX.p.ball 0 1) \ radialGoodSet Δ) := by
      rw [← Set.image_union]
      congr 1
      ext x
      simp [G, radialGoodSet]
    rw [hsplit]
    exact measure_congr (union_ae_eq_left_of_ae_eq_empty
      (ae_eq_empty.mpr (radial_image_badSet_null Δ))).symm
  calc
    (∫⁻ x in (MX.p.ball 0 1),
        ENNReal.ofReal |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume) =
        ∫⁻ x in G,
          ENNReal.ofReal |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume := hdomain
    _ = volume (radialMap Δ '' G) := by
      simpa only [ContinuousLinearMap.det] using harea
    _ = volume ((MY.p.ball 0 1)) := himage

private theorem modelOpenBall_volume_eq_ballVolume {m : ℕ}
    (M : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    (volume (M.p.ball 0 1)).toReal = M.closedUnitBallVolume := by
  have hsphere : {x | M.p x = 1} = frontier (M.p.ball 0 1) := by
    ext x
    change M.p x = 1 ↔ x ∈ frontier (M.p.ball 0 1)
    rw [← congrFun M.p.gauge_ball x]
    exact gauge_eq_one_iff_mem_frontier (M.p.convex_ball 0 1)
      (M.p.ball_mem_nhds M.continuous_p zero_lt_one)
  have hnull : volume {x | M.p x = 1} = 0 := by
    rw [hsphere]
    exact (M.p.convex_ball 0 1).addHaar_frontier volume
  unfold EquivalentSeminorm.closedUnitBallVolume
  apply congrArg ENNReal.toReal
  exact measure_congr (by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    have hne : M.p x ≠ 1 := hx
    apply propext
    change x ∈ M.p.ball 0 1 ↔ x ∈ M.closedUnitBall
    simp only [Seminorm.mem_ball_zero, EquivalentSeminorm.mem_closedUnitBall]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩)

/-- Absolute Jacobian area identity in reference coordinates and the fixed
Lebesgue normalization, retaining the exact positive-dimensional source bound. -/
theorem radialExtension_integral_abs_det {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∫ x in MX.p.ball 0 1,
      |ContinuousLinearMap.det (fderiv ℝ (fun y : Fin (m + 1) → ℝ =>
        (show Fin (m + 1) → ℝ from radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from y))) x)|
      ∂volume = MY.closedUnitBallVolume := by
  change (∫ x in MX.p.ball 0 1,
    |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume) = _
  have hlin := radial_lintegral_abs_det_eq_openBall_volume Δ
  have hint : IntegrableOn
      (fun x => |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)|)
      (MX.p.ball 0 1) volume :=
    (radial_abs_det_integrableOn Δ).mono_set
      (by intro x hx; exact MX.mem_closedUnitBall.mpr (le_of_lt (by simpa using hx)))
  have hnonneg_ae : 0 ≤ᵐ[volume.restrict (MX.p.ball 0 1)]
      fun x => |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| :=
    ae_of_all _ fun x => abs_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg_ae] at hlin
  have hto := congrArg ENNReal.toReal hlin
  have hnonneg : 0 ≤ ∫ x in MX.p.ball 0 1,
      |ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x)| ∂volume :=
    integral_nonneg_of_ae hnonneg_ae
  rw [ENNReal.toReal_ofReal hnonneg] at hto
  exact hto.trans (modelOpenBall_volume_eq_ballVolume MY)

namespace Internal
private def PiolaOrientation_modelRadialData {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    BilipschitzOrientation.BiLipschitzOpenData (m + 1) where
  source := MX.p.ball 0 1
  target := MY.p.ball 0 1
  source_open := openBall_isOpen MX
  target_open := openBall_isOpen MY
  f := radialMap Δ
  g := radialMap Δ.symm
  mapsTo_f := by intro x hx; simpa using hx
  mapsTo_g := by intro x hx; simpa using hx
  left_inv := by intro x _; exact radialMap_leftInverse Δ x
  right_inv := by intro x _; exact radialMap_leftInverse Δ.symm x
  fConstant := (3 * MX.upper / MY.lower).toNNReal
  lipschitzWith_f := radialMap_lipschitz Δ
  gConstant := (3 * MY.upper / MX.lower).toNNReal
  lipschitzWith_g := radialMap_lipschitz Δ.symm
  lower := referenceAntiConstant MX MY
  lower_pos := referenceAntiConstant_pos MX MY
  anti := radialMap_lower Δ

private theorem piolaData_connected {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    IsConnected (PiolaOrientation_modelRadialData Δ).source ∧
    IsConnected (PiolaOrientation_modelRadialData Δ).target :=
  ⟨openBall_connected MX, openBall_connected MY⟩
end Internal

private theorem source_B67 {m : ℕ} (M : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    0 < volume (M.p.ball 0 1) := by
  have hreal : 0 < (volume (M.p.ball 0 1)).toReal := by
    rw [modelOpenBall_volume_eq_ballVolume M]
    exact M.closedUnitBallVolume_pos
  exact (ENNReal.toReal_pos_iff.mp hreal).1

private theorem source_B68 {m : ℕ} (M : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    volume (M.p.ball 0 1) ≠ ∞ := by
  exact ne_top_of_le_ne_top M.closedUnitBall_isCompact.measure_ne_top
    (measure_mono (by
      intro x hx
      exact M.mem_closedUnitBall.mpr (le_of_lt (by simpa using hx))))

end MathlibAnnex.Sphere
