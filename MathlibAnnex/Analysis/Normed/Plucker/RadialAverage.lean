import MathlibAnnex.Analysis.Normed.Plucker.Average
import MathlibAnnex.Analysis.Normed.Sphere.RadialJacobian
import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import MathlibAnnex.Analysis.Calculus.BilipschitzOrientation

/-! # Linear transport of radial derivative averages

Derivatives use the reference finite Pi norm. The radial extension goes from
`Space MX` to `Space MY`, and the linear map is composed on its left.
Increasing selected rows and the original Lebesgue ball volumes are fixed.
The signed integral uses the accepted degree-free orientation theorem, with
an explicit real scalar equal to `1` or `-1`. The pointwise composition formula
includes dimension zero; the radial integral and average keep `m + 1`.
-/

noncomputable section
open Set Metric Function MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace MathlibAnnex.Plucker
open EquivalentSeminorm Sphere

-- Reference-coordinate adapters are reconstructed from the exact B2 source.
-- SR-SOURCE-B31: the superseded radial-map alias is private definitional glue.
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


-- SR-SOURCE-B32: the source alias equality is definitional.
example {n : ℕ} {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    radialMap Δ = (fun x : Fin n → ℝ => (show Fin n → ℝ from
      radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x))) := rfl

-- SR-SOURCE-B48: expand the original existential Lipschitz abbreviation.
private theorem source_B48 {n : ℕ} {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∃ C : ℝ≥0, LipschitzWith C (radialMap Δ) := ⟨_, radialMap_lipschitz Δ⟩

-- SR-SOURCE-B211: retain the exact nonempty-open-set volume argument.
private theorem source_B211 {n : ℕ} {V : Set (Fin n → ℝ)}
    (hVo : IsOpen V) (hVne : V.Nonempty) : 0 < volume V := by
  exact Measure.measure_pos_of_nonempty_interior volume
    (by simpa [hVo.interior_eq] using hVne)

-- SR-SOURCE-B53 and B54 remain private recovery support; the signed proof
-- itself uses the global orientation theorem without choosing a point.
private theorem source_B53 {n : ℕ} (_hn : 0 < n)
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∃ x ∈ MX.p.ball 0 1, DifferentiableAt ℝ (radialMap Δ) x := by
  have hopen := openBall_isOpen MX
  have hne : (MX.p.ball 0 1).Nonempty := ⟨0, by simp⟩
  have hpos : volume (MX.p.ball 0 1) ≠ 0 := (source_B211 hopen hne).ne'
  have hdiff : ∀ᵐ x ∂volume.restrict (MX.p.ball 0 1),
      DifferentiableAt ℝ (radialMap Δ) x := ae_restrict_of_ae (source_B52 Δ)
  have hmem : ∀ᵐ x ∂volume.restrict (MX.p.ball 0 1), x ∈ MX.p.ball 0 1 :=
    ae_restrict_mem hopen.measurableSet
  haveI : (ae (volume.restrict (MX.p.ball 0 1))).NeBot :=
    MeasureTheory.ae_restrict_neBot.mpr hpos
  rcases (hmem.and hdiff).exists with ⟨x, hxmem, hxdiff⟩
  exact ⟨x, hxmem, hxdiff⟩

private theorem source_B54 {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∃ x ∈ MX.p.ball 0 1, DifferentiableAt ℝ (radialMap Δ) x :=
  source_B53 (Nat.succ_pos m) Δ

-- SR-SOURCE-B243: the old coordinate vector is exactly Pi.single.
private theorem referenceMatrix_apply {n N : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (i : Fin N) (j : Fin n) :
    LinearMap.toMatrix' A.toLinearMap i j = A (Pi.single j 1) i := rfl

namespace Internal
-- SR-SOURCE-B26: all original witness fields, with the accepted scalar sign.
private structure SignedRadialData {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) where
  radial : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)
  lipschitz : ∃ C : ℝ≥0, LipschitzWith C radial
  onSphere : ∀ u : MX.unitSphere,
    radial u.val = (show Fin (m + 1) → ℝ from
      (Δ ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩).val)
  average_linear_comp : ∀ {N : ℕ}
      (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)), MY.IsContraction A →
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        derivativeAverage MX (fun x => A (radial x)) =
          ε • Matrix.ballVolumeScaledMaximalMinors MY A
end Internal

/-- Linear composition multiplies each derivative generator coordinate by the
signed square determinant of the inner derivative. Valid also for `n = 0`. -/
theorem derivativeGenerator_comp_linear_apply {n N : ℕ}
    (MX : EquivalentSeminorm (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ))
    (H : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (s : Matrix.MaximalMinorIndex n (Fin N)) (hH : DifferentiableAt ℝ H x) :
    derivativeGenerator MX (fun z => A (H z)) x s =
      MX.closedUnitBallVolume * Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) s *
        ContinuousLinearMap.det (fderiv ℝ H x) := by
  have hcomp : fderiv ℝ (fun z => A (H z)) x = A.comp (fderiv ℝ H x) :=
    (A.hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  change MX.closedUnitBallVolume * Matrix.maximalMinor
    (LinearMap.toMatrix' (fderiv ℝ (fun z => A (H z)) x).toLinearMap) s = _
  rw [hcomp]
  change MX.closedUnitBallVolume * Matrix.maximalMinor
    (LinearMap.toMatrix' (A.toLinearMap.comp (fderiv ℝ H x).toLinearMap)) s = _
  rw [LinearMap.toMatrix'_comp, Matrix.maximalMinor_mul, LinearMap.det_toMatrix']
  simp only [ContinuousLinearMap.det, mul_assoc]

namespace Internal
private theorem derivativePlucker_linear_radial_apply_ae {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ))
    (s : Matrix.MaximalMinorIndex (m + 1) (Fin N)) :
    ∀ᵐ x ∂volume.restrict MX.closedUnitBall,
      derivativeGenerator MX (fun z => A (radialMap Δ z)) x s =
        MX.closedUnitBallVolume * Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) s *
          ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) := by
  have hae : ∀ᵐ x ∂volume.restrict MX.closedUnitBall,
      DifferentiableAt ℝ (radialMap Δ) x :=
    (radialMap_lipschitz Δ).ae_differentiableAt.filter_mono ae_restrict_le
  filter_upwards [hae] with x hx
  exact derivativeGenerator_comp_linear_apply MX A (radialMap Δ) x s hx

private theorem sphereSet_null {m : ℕ} (M : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    volume {x | M.p x = 1} = 0 := by
  have hsphere : {x | M.p x = 1} = frontier (M.p.ball 0 1) := by
    ext x
    change M.p x = 1 ↔ x ∈ frontier (M.p.ball 0 1)
    rw [← congrFun M.p.gauge_ball x]
    exact gauge_eq_one_iff_mem_frontier (M.p.convex_ball 0 1)
      (M.p.ball_mem_nhds M.continuous_p zero_lt_one)
  rw [hsphere]
  exact (M.p.convex_ball 0 1).addHaar_frontier volume

private theorem integral_coordDet_unitBall_eq_openBall {m : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    ∫ x in MX.closedUnitBall, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume =
      ∫ x in MX.p.ball 0 1, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume := by
  apply setIntegral_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (sphereSet_null MX)] with x hx
  have hne : MX.p x ≠ 1 := hx
  apply propext
  change x ∈ MX.closedUnitBall ↔ x ∈ MX.p.ball 0 1
  rw [EquivalentSeminorm.mem_closedUnitBall, Seminorm.mem_ball_zero]
  exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
end Internal
open Internal

/-- Each coordinate of the radial derivative average is the corresponding
linear maximal minor times the signed determinant integral over the source ball. -/
theorem derivativeAverage_comp_linear_radial_apply {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ))
    (q : Matrix.MaximalMinorIndex (m + 1) (Fin N)) :
    derivativeAverage MX (fun x => A (show Fin (m + 1) → ℝ from
      radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x))) q =
      Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) q *
        ∫ x in MX.p.ball 0 1,
          ContinuousLinearMap.det (fderiv ℝ (fun y : Fin (m + 1) → ℝ =>
            (show Fin (m + 1) → ℝ from radialExtension (X := Space MX) (Y := Space MY) Δ
              (show Space MX from y))) x) ∂volume := by
  change derivativeAverage MX (fun x => A (radialMap Δ x)) q =
    Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) q *
      ∫ x in MX.p.ball 0 1, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume
  have hcongr :
      (∫ x in MX.closedUnitBall, derivativeGenerator MX (fun z => A (radialMap Δ z)) x q ∂volume) =
      ∫ x in MX.closedUnitBall,
        (MX.closedUnitBallVolume * Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) q) *
          ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume := by
    apply integral_congr_ae
    exact (derivativePlucker_linear_radial_apply_ae Δ A q).mono
      (fun _ hx => by simpa [mul_assoc] using hx)
  have hint := derivativeGenerator_integrableOn_compact MX
    ⟨_, A.lipschitz.comp (radialMap_lipschitz Δ)⟩ MX.closedUnitBall_isCompact
  have hcoord : ∀ t : Matrix.MaximalMinorIndex (m + 1) (Fin N),
      Integrable (fun x => derivativeGenerator MX (fun z => A (radialMap Δ z)) x t)
        (volume.restrict MX.closedUnitBall) := fun t => hint.eval t
  rw [derivativeAverage, setAverage_eq, Pi.smul_apply,
    MeasureTheory.eval_integral hcoord q, hcongr,
    integral_const_mul, integral_coordDet_unitBall_eq_openBall Δ]
  change MX.closedUnitBallVolume⁻¹ * (MX.closedUnitBallVolume *
    Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) q *
      (∫ x in MX.p.ball 0 1, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume)) = _
  rw [mul_assoc MX.closedUnitBallVolume, ← mul_assoc MX.closedUnitBallVolume⁻¹,
    inv_mul_cancel₀ (ne_of_gt MX.closedUnitBallVolume_pos), one_mul]

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

namespace Internal
private def radialOpenData {m : ℕ}
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
    IsConnected (radialOpenData Δ).source ∧
    IsConnected (radialOpenData Δ).target :=
  ⟨openBall_connected MX, openBall_connected MY⟩
end Internal


/-- The full radial average is exactly one orientation sign times the target
generator. No contraction hypothesis on the linear map is introduced. -/
theorem derivativeAverage_comp_linear_radial {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      derivativeAverage MX (fun x => A (show Fin (m + 1) → ℝ from
        radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x))) =
        ε • Matrix.ballVolumeScaledMaximalMinors MY A := by
  let D := radialOpenData Δ
  have hpos : 0 < volume D.target := by
    change 0 < volume (MY.p.ball 0 1)
    exact source_B211 (openBall_isOpen MY) ⟨0, by simp⟩
  have hfinite : volume D.target ≠ ∞ :=
    ne_top_of_le_ne_top MY.closedUnitBall_isCompact.measure_ne_top
      (measure_mono (by
        intro x hx
        exact MY.mem_closedUnitBall.mpr (le_of_lt (by simpa [D, radialOpenData] using hx))))
  obtain ⟨ε, hε, hs⟩ := BilipschitzOrientation.integral_det_fderiv_eq_signed_volume
    D (piolaData_connected Δ).2.isPreconnected hpos hfinite
  change (∫ x in MX.p.ball 0 1, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume) =
    ε * (volume (MY.p.ball 0 1)).toReal at hs
  rw [modelOpenBall_volume_eq_ballVolume MY] at hs
  refine ⟨ε, hε, ?_⟩
  ext q
  rw [derivativeAverage_comp_linear_radial_apply Δ A q]
  change Matrix.maximalMinor (LinearMap.toMatrix' A.toLinearMap) q *
    (∫ x in MX.p.ball 0 1, ContinuousLinearMap.det (fderiv ℝ (radialMap Δ) x) ∂volume) = _
  rw [hs]
  simp only [Pi.smul_apply, Matrix.ballVolumeScaledMaximalMinors,
    Matrix.maximalMinors, smul_eq_mul]
  ring

namespace Internal
private def PiolaOrientation_concreteSignedRadialData {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    SignedRadialData MX MY Δ where
  radial := radialMap Δ
  lipschitz := source_B48 Δ
  onSphere := by
    intro u
    exact radialExtension_on_sphere Δ
      ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩
  average_linear_comp := by
    intro N A _hA
    exact derivativeAverage_comp_linear_radial Δ A
end Internal
end MathlibAnnex.Plucker
