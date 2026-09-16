import MathlibAnnex.Analysis.Normed.Operator.PluckerSupport
import MathlibAnnex.Analysis.Convex.PluckerBody
import MathlibAnnex.Analysis.Convex.LexicographicSelection

noncomputable section
set_option autoImplicit false
open Set Module
open scoped BigOperators NNReal
namespace MathlibAnnex.FiniteRecovery
universe u
open Satellite
private abbrev Coord (n : ℕ) := Fin n → ℝ
private abbrev NormModel (n : ℕ) := EquivalentSeminorm (Coord n)
private abbrev DualFrame (n : ℕ) := DeterminantFrame.Frame n (Coord n)
private abbrev dualFrameMatrix {n : ℕ} := DeterminantFrame.frameMatrix (Pi.basisFun ℝ (Fin n))
private abbrev frameDet {n : ℕ} := DeterminantFrame.frameDeterminant (Pi.basisFun ℝ (Fin n))
private abbrev replacementDet {n : ℕ} := DeterminantFrame.replacementDeterminant (Pi.basisFun ℝ (Fin n))
private abbrev frameCoordinates {n : ℕ} := @DeterminantFrame.frameCoordinates n (Coord n) _ _
private abbrev framePreimage {n : ℕ} (B : DualFrame n) (c : Coord n) := (dualFrameMatrix B)⁻¹.mulVec c
private abbrev IsDualContraction {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) := ∀ x, |r x| ≤ M.p x
private abbrev dualRowSet {n : ℕ} (M : NormModel n) := {r : Coord n →L[ℝ] ℝ | IsDualContraction M r}
private abbrev dualFrameSet {n : ℕ} (M : NormModel n) := {B : DualFrame n | ∀ i, IsDualContraction M (B i)}

private instance modelFiniteDimensional {n : ℕ} (M : NormModel n) : FiniteDimensional ℝ (EquivalentSeminorm.Space M) :=
  inferInstanceAs (FiniteDimensional ℝ (Coord n))

private def modelBasis {n : ℕ} (M : NormModel n) : Basis (Fin n) ℝ (EquivalentSeminorm.Space M) :=
  Pi.basisFun ℝ (Fin n)

private def toModelRow {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) :
    EquivalentSeminorm.Space M →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (show EquivalentSeminorm.Space M →ₗ[ℝ] ℝ from r.toLinearMap)

private def fromModelRow {n : ℕ} (M : NormModel n) (r : EquivalentSeminorm.Space M →L[ℝ] ℝ) :
    Coord n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (show Coord n →ₗ[ℝ] ℝ from r.toLinearMap)

private theorem toModelRow_mem_iff {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) :
    toModelRow M r ∈ DeterminantFrame.unitRowSet (EquivalentSeminorm.Space M) ↔ IsDualContraction M r := by
  rw [DeterminantFrame.mem_unitRowSet]
  constructor
  · intro h x
    have := (toModelRow M r).le_opNorm (show EquivalentSeminorm.Space M from x)
    change |r x| ≤ ‖toModelRow M r‖ * M.p x at this
    exact this.trans (by nlinarith [apply_nonneg M.p x])
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change |r (show Coord n from x)| ≤ 1 * M.p (show Coord n from x)
    simpa only [one_mul] using h (show Coord n from x)

private abbrev detMax {n : ℕ} (M : NormModel n) := DeterminantFrame.determinantMaximum (modelBasis M)
private abbrev NearMaxInverseBound {n : ℕ} (M : NormModel n) := DeterminantFrame.NearMaxInverseBound (modelBasis M)
private abbrev nearMaxFrames {n : ℕ} (M : NormModel n) (η : ℝ) := {B : DualFrame n | B ∈ dualFrameSet M ∧ detMax M - η ≤ |frameDet B|}

private theorem toModelFrame_mem {n : ℕ} (M : NormModel n) {B : DualFrame n} (h : B ∈ dualFrameSet M) :
    (fun i => toModelRow M (B i)) ∈ DeterminantFrame.unitFrameSet n (EquivalentSeminorm.Space M) := by
  intro i
  exact (toModelRow_mem_iff M (B i)).mpr (h i)

private theorem toModelFrame_near {n : ℕ} (M : NormModel n) {η : ℝ} {B : DualFrame n} (h : B ∈ nearMaxFrames M η) :
    (fun i => toModelRow M (B i)) ∈ DeterminantFrame.nearMaxFrames (modelBasis M) η :=
  ⟨toModelFrame_mem M h.1, h.2⟩

private theorem inverseBound {n : ℕ} (M : NormModel n) {η : ℝ} (H : NearMaxInverseBound M η) {B : DualFrame n}
    (h : B ∈ nearMaxFrames M η) (c : Coord n) : M.p (framePreimage B c) ≤ H.K * ‖c‖ := by
  exact H.bound (toModelFrame_near M h) c

private theorem detMax_pos {n : ℕ} (M : NormModel n) : 0 < detMax M :=
  DeterminantFrame.determinantMaximum_pos (modelBasis M)

private theorem nearMaxFrame_det_ne_zero {n : ℕ} (M : NormModel n) {η : ℝ}
    (hη : η < detMax M) {B : DualFrame n} (hB : B ∈ nearMaxFrames M η) : frameDet B ≠ 0 :=
  DeterminantFrame.nearMaxFrame_det_ne_zero (modelBasis M) hη (toModelFrame_near M hB)

private theorem inverse_mulVec_frameCoordinates {n : ℕ} (M : NormModel n) {η : ℝ}
    (hη : η < detMax M) {B : DualFrame n} (hB : B ∈ nearMaxFrames M η) (x : Coord n) :
    framePreimage B (frameCoordinates B x) = x := by
  exact DeterminantFrame.inverse_mulVec_frameCoordinates (modelBasis M) hη (toModelFrame_near M hB) (show EquivalentSeminorm.Space M from x)

private theorem abs_replacementDet_le_detMax {n : ℕ} (M : NormModel n) {B : DualFrame n} (hB : B ∈ dualFrameSet M)
    (i : Fin n) {r : Coord n →L[ℝ] ℝ} (hr : IsDualContraction M r) : |replacementDet B i r| ≤ detMax M := by
  have h := DeterminantFrame.abs_replacementDeterminant_le_maximum (modelBasis M) (toModelFrame_mem M hB) i ((toModelRow_mem_iff M r).mpr hr)
  have heq : (fun j => toModelRow M ((DeterminantFrame.replaceRow B i r) j)) =
      DeterminantFrame.replaceRow (fun j => toModelRow M (B j)) i (toModelRow M r) := by
    funext j
    by_cases hj : j = i <;> simp [DeterminantFrame.replaceRow, hj]
  change |DeterminantFrame.frameDeterminant (modelBasis M)
    (fun j => toModelRow M ((DeterminantFrame.replaceRow B i r) j))| ≤ detMax M
  rw [heq]
  exact h

private def maxFrame {n : ℕ} (M : NormModel n) : DualFrame n :=
  fun i => fromModelRow M (DeterminantFrame.maximizingFrame (modelBasis M) i)

private theorem maxFrame_det {n : ℕ} (M : NormModel n) : |frameDet (maxFrame M)| = detMax M := rfl

private theorem maxFrame_mem {n : ℕ} (M : NormModel n) : maxFrame M ∈ dualFrameSet M := by
  intro i
  apply (toModelRow_mem_iff M _).mp
  have h := DeterminantFrame.maximizingFrame_mem (modelBasis M) i
  convert h using 1
  ext x
  rfl


private abbrev replaceFrameRow {n : ℕ} := @DeterminantFrame.replaceRow n (Coord n) _ _
private abbrev functionalRow {n : ℕ} := DeterminantFrame.functionalCoordinates (Pi.basisFun ℝ (Fin n))
private theorem frameDet_continuous {n : ℕ} : Continuous (frameDet : DualFrame n → ℝ) :=
  DeterminantFrame.frameDeterminant_continuous (Pi.basisFun ℝ (Fin n))
private theorem dualFrameMatrix_replaceFrameRow {n : ℕ} (B : DualFrame n) (i : Fin n) (r : Coord n →L[ℝ] ℝ) :
    dualFrameMatrix (replaceFrameRow B i r) = (dualFrameMatrix B).updateRow i (functionalRow r) :=
  DeterminantFrame.frameMatrix_replaceRow (Pi.basisFun ℝ (Fin n)) B i r
private theorem cramerReplacement {n : ℕ} (B : DualFrame n) (hB : frameDet B ≠ 0) (r : Coord n →L[ℝ] ℝ) (c : Coord n) :
    (∑ i : Fin n, c i * replacementDet B i r) = frameDet B * r (framePreimage B c) :=
  DeterminantFrame.cramerReplacement (Pi.basisFun ℝ (Fin n)) B hB r c

private theorem dualRowSet_isCompact {n : ℕ} (M : NormModel n) : IsCompact (dualRowSet M) := by
  have hc : IsClosed (dualRowSet M) := by
    have heq : dualRowSet M = (⋂ x : Coord n, {r : Coord n →L[ℝ] ℝ | |r x| ≤ M.p x}) := by ext r; simp [dualRowSet, IsDualContraction]
    rw [heq]
    exact isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const
  have hb : Bornology.IsBounded (dualRowSet M) := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : Coord n →L[ℝ] ℝ)).2
    refine ⟨M.upper, ?_⟩
    intro r hr
    rw [Metric.mem_closedBall, dist_zero_right]
    apply ContinuousLinearMap.opNorm_le_bound _ M.upper_pos.le
    intro x
    exact (hr x).trans (M.le_upper x)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

private theorem dualFrameSet_isCompact {n : ℕ} (M : NormModel n) : IsCompact (dualFrameSet M) := by
  have heq : dualFrameSet M = Set.univ.pi (fun _ : Fin n => dualRowSet M) := by ext B; simp [dualFrameSet, dualRowSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => dualRowSet_isCompact M


private abbrev SupCoord (n : ℕ) := Fin n → ℝ

variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}
private noncomputable instance centerFintype (C : FiniteCoefficientNet (n := n) K ρ) :
    Fintype C.centers :=
  C.centers_finite.fintype



variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}
private def centerValue (C : FiniteCoefficientNet (n := n) K ρ) (c : C.centers) :
    Coord n := c.1

private def satelliteRadius (ε K : ℝ) : ℝ := min ε 1 / (8 * K)

private theorem satelliteRadius_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    0 < satelliteRadius ε K := by
  exact div_pos (lt_min hε zero_lt_one) (mul_pos (by norm_num) hK)

private theorem two_mul_K_mul_satelliteRadius_lt_half {ε K : ℝ}
    (hε : 0 < ε) (hK : 0 < K) :
    2 * K * satelliteRadius ε K < ε / 2 := by
  have hden : 0 < 8 * K := mul_pos (by norm_num) hK
  have hmin : min ε 1 ≤ ε := min_le_left _ _
  unfold satelliteRadius
  calc
    2 * K * (min ε 1 / (8 * K)) = min ε 1 / 4 := by field_simp; ring
    _ ≤ ε / 4 := by linarith
    _ < ε / 2 := by linarith

private theorem satelliteRadius_lt_half_inv {ε K : ℝ}
    (_hε : 0 < ε) (hK : 0 < K) :
    satelliteRadius ε K < 1 / (2 * K) := by
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  unfold satelliteRadius
  have hK2 : 0 < 2 * K := mul_pos (by norm_num) hK
  have hK8 : 0 < 8 * K := mul_pos (by norm_num) hK
  calc
    min ε 1 / (8 * K) ≤ 1 / (8 * K) :=
      div_le_div_of_nonneg_right hmin hK8.le
    _ < 1 / (2 * K) := by
      apply one_div_lt_one_div_of_lt hK2
      nlinarith

private noncomputable def satelliteRadiusNNReal (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    ℝ≥0 :=
  ⟨satelliteRadius ε K, (satelliteRadius_pos hε hK).le⟩

@[simp] private theorem coe_satelliteRadiusNNReal (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    (satelliteRadiusNNReal ε K hε hK : ℝ) = satelliteRadius ε K := rfl

private theorem satelliteRadiusNNReal_ne_zero {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    satelliteRadiusNNReal ε K hε hK ≠ 0 := by
  exact ne_of_gt (by
    change 0 < satelliteRadius ε K
    exact satelliteRadius_pos hε hK)

private theorem satelliteRowsSet_isCompact {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] :
    IsCompact (satelliteRowsSet M J) := by
  have heq : satelliteRowsSet M J =
      Set.univ.pi (fun _ : J => dualRowSet M) := by
    ext sat
    simp [satelliteRowsSet, dualRowSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => dualRowSet_isCompact M

private theorem satelliteConfigurationSet_isCompact {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] :
    IsCompact (satelliteConfigurationSet M J) := by
  exact (dualFrameSet_isCompact M).prod (satelliteRowsSet_isCompact M J)

private theorem satelliteConfigurationSet_nonempty {n : ℕ} (M : NormModel n)
    (J : Type u) :
    (satelliteConfigurationSet M J).Nonempty := by
  refine ⟨((fun _ => 0), fun _ => 0), ?_⟩
  constructor
  · intro i x
    simpa only [zero_apply, abs_zero] using (apply_nonneg M.p x)
  · intro a x
    simpa only [zero_apply, abs_zero] using (apply_nonneg M.p x)

private theorem configurationPolynomial_continuous {n : ℕ} {J : Type u} [Fintype J]
    (weight : ℝ) (coeff : J → Coord n) :
    Continuous (configurationPolynomial weight coeff) := by
  change Continuous fun C : SatelliteConfiguration n J =>
    weight * frameDet C.1 +
      ∑ a : J, ∑ i : Fin n,
        coeff a i * replacementDet C.1 i (C.2 a)
  have hreplacement : ∀ (a : J) (i : Fin n),
      Continuous fun C : SatelliteConfiguration n J =>
        replacementDet C.1 i (C.2 a) := by
    intro a i
    unfold replacementDet DeterminantFrame.replacementDeterminant DeterminantFrame.frameDeterminant
    apply Continuous.matrix_det
    apply continuous_matrix
    intro k j
    simp only [DeterminantFrame.frameMatrix, Pi.basisFun_apply]
    change Continuous fun C : SatelliteConfiguration n J =>
      (replaceFrameRow C.1 i (C.2 a)) k (Pi.single j 1)
    by_cases hki : k = i
    · subst k
      simpa [replaceFrameRow, DeterminantFrame.replaceRow] using
        (show Continuous fun C : SatelliteConfiguration n J =>
          C.2 a (Pi.single j 1) by fun_prop)
    · simpa [replaceFrameRow, DeterminantFrame.replaceRow, hki] using
        (show Continuous fun C : SatelliteConfiguration n J =>
          C.1 k (Pi.single j 1) by fun_prop)
  apply Continuous.add
  · exact continuous_const.mul (frameDet_continuous.comp continuous_fst)
  · exact continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun i _ =>
        continuous_const.mul (hreplacement a i)

private theorem exists_maxSatelliteConfiguration {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n) :
    ∃ C ∈ satelliteConfigurationSet M J,
      ∀ D ∈ satelliteConfigurationSet M J,
        |configurationPolynomial weight coeff D| ≤
          |configurationPolynomial weight coeff C| := by
  rcases (satelliteConfigurationSet_isCompact M J).exists_isMaxOn
      (satelliteConfigurationSet_nonempty M J)
      (configurationPolynomial_continuous weight coeff).abs.continuousOn with
    ⟨C, hC, hmax⟩
  exact ⟨C, hC, hmax⟩

private theorem maxSatelliteConfiguration_mem {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n) :
    maxSatelliteConfiguration M J weight coeff ∈
      satelliteConfigurationSet M J :=
  (Classical.choose_spec
    (exists_maxSatelliteConfiguration M J weight coeff)).1

private theorem abs_configurationPolynomial_le_max {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J) :
    |configurationPolynomial weight coeff C| ≤
      |configurationPolynomial weight coeff
        (maxSatelliteConfiguration M J weight coeff)| :=
  (Classical.choose_spec
    (exists_maxSatelliteConfiguration M J weight coeff)).2 C hC

private theorem maxNetSatelliteConfiguration_satellites_one_sub_epsilon
    {n : ℕ} (M : NormModel n) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (C : FiniteCoefficientNet (n := n) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue C) < weight * η)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ a : C.centers,
      1 - ε <
        |(maxSatelliteConfiguration M C.centers weight (centerValue C)).2 a x| := by
  let Q := maxSatelliteConfiguration M C.centers weight (centerValue C)
  have hQ : Q ∈ satelliteConfigurationSet M C.centers := by
    exact maxSatelliteConfiguration_mem M C.centers weight (centerValue C)
  have hmax : ∀ D ∈ satelliteConfigurationSet M C.centers,
      |configurationPolynomial weight (centerValue C) D| ≤
        |configurationPolynomial weight (centerValue C) Q| := by
    intro D hD
    simpa [Q] using abs_configurationPolynomial_le_max
      M C.centers weight (centerValue C) hD
  simpa [Q] using finiteNet_absoluteMaximizer_satellites_one_sub_epsilon
    M hη0 hηD hε H C hweight hgap hQ hmax hx

open FiniteSup FiniteSup.Bridge PluckerSupport
namespace Internal
end Internal
open Internal

private abbrev PluckerCoord (n N : ℕ) := MathlibAnnex.Matrix.MaximalMinorIndex n (Fin N) → ℝ
private abbrev positiveSatelliteAmbientDim (m : ℕ) (J : Type u) [Fintype J] := (m + 1) + Fintype.card J
private abbrev CompactRawSet := TopologicalSpace.NonemptyCompacts
private def supportOrientation (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1
private theorem supportOrientation_mem (t : ℝ) : supportOrientation t = 1 ∨ supportOrientation t = -1 := by
  by_cases ht : 0 ≤ t
  · exact Or.inl (by simp [supportOrientation, ht])
  · exact Or.inr (by simp [supportOrientation, ht])

private noncomputable def Internal.rawPluckerCompact {n N : ℕ} (M : NormModel n) :
    CompactRawSet (PluckerCoord n N) where
  carrier := MathlibAnnex.PluckerBody.generators M N
  isCompact' := MathlibAnnex.PluckerBody.generators_isCompact M
  nonempty' := MathlibAnnex.PluckerBody.generators_nonempty M

def PluckerGeneratorGood {n N : ℕ} (M : NormModel n) (ε : ℝ)
    (z : PluckerCoord n N) : Prop :=
  ∃ A : Coord n →L[ℝ] SupCoord N,
    M.IsContraction A ∧
    FinMapAlmostIsometric M ε A ∧
    (z = MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A ∨ z = - MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A)

private theorem sign_mul_le_abs {s t : ℝ} (hs : s = 1 ∨ s = -1) :
    s * t ≤ |t| := by
  rcases hs with rfl | rfl
  · simpa using le_abs_self t
  · simpa using neg_le_abs t

private theorem Internal.abs_eq_of_oriented_signed_scaled_eq
    {v s τ p q : ℝ} (hv : 0 < v)
    (hs : s = 1 ∨ s = -1) (hτ : τ = 1 ∨ τ = -1)
    (h : v * (τ * (s * p)) = v * |q|) :
    |p| = |q| := by
  have hscalar : τ * (s * p) = |q| := by
    nlinarith
  have habs := congrArg abs hscalar
  rcases hs with rfl | rfl <;> rcases hτ with rfl | rfl <;>
    simpa using habs

private theorem Internal.selectedNormalizedPlucker_mem_raw
    {m : ℕ} {J : Type u} [Fintype J]
    (M : NormModel (m + 1)) (weight : ℝ)
    (coeff : J → Coord (m + 1)) :
    MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M
      (configurationFinMap
        (maxSatelliteConfiguration M J weight coeff)) ∈
      MathlibAnnex.PluckerBody.generators M (positiveSatelliteAmbientDim m J) := by
  have hC := maxSatelliteConfiguration_mem M J weight coeff
  exact ⟨configurationFinMap (maxSatelliteConfiguration M J weight coeff),
    (configuration_contraction_iff M _).2 hC, Or.inl rfl⟩

theorem rawOrientedSupportMaximizer_isAbsolutePolynomialMaximizer
    {m : ℕ} {J : Type u} [Fintype J]
    (M : NormModel (m + 1)) (weight : ℝ)
    (coeff : J → Coord (m + 1))
    {z : PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J)}
    (hz : z ∈ MathlibAnnex.NonemptyCompacts.maxSlice (rawPluckerCompact
      (N := positiveSatelliteAmbientDim m J) M)
        (orientedSatelliteSupport weight coeff
          (maxSatelliteConfiguration M J weight coeff))) :
    ∃ A : Coord (m + 1) →L[ℝ]
        SupCoord (positiveSatelliteAmbientDim m J),
      M.IsContraction A ∧
      (z = MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A ∨ z = - MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) ∧
      let C := finMapConfiguration A
      C ∈ satelliteConfigurationSet M J ∧
      ∀ D ∈ satelliteConfigurationSet M J,
        |configurationPolynomial weight coeff D| ≤
          |configurationPolynomial weight coeff C| := by
  classical
  let Cstar : SatelliteConfiguration (m + 1) J :=
    maxSatelliteConfiguration M J weight coeff
  let R := rawPluckerCompact (N := positiveSatelliteAmbientDim m J) M
  let ℓ := orientedSatelliteSupport weight coeff Cstar
  have hCstar : Cstar ∈ satelliteConfigurationSet M J := by
    simpa [Cstar] using maxSatelliteConfiguration_mem M J weight coeff
  have hstarMax : ∀ D ∈ satelliteConfigurationSet M J,
      |configurationPolynomial weight coeff D| ≤
        |configurationPolynomial weight coeff Cstar| := by
    intro D hD
    simpa [Cstar] using abs_configurationPolynomial_le_max M J weight coeff hD
  have hstarRaw : MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap Cstar) ∈ (R : Set _) := by
    change MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap Cstar) ∈
      MathlibAnnex.PluckerBody.generators M (positiveSatelliteAmbientDim m J)
    simpa [Cstar] using selectedNormalizedPlucker_mem_raw M weight coeff
  have hstarLeZ :
      ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap Cstar)) ≤ ℓ z := by
    calc
      ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap Cstar))
          ≤ MathlibAnnex.NonemptyCompacts.maxValue R ℓ := MathlibAnnex.NonemptyCompacts.le_maximizer R ℓ hstarRaw
      _ = ℓ z := hz.2.symm
  rcases hz.1 with ⟨A, hA, hzPos | hzNeg⟩
  · let C : SatelliteConfiguration (m + 1) J := finMapConfiguration A
    have hC : C ∈ satelliteConfigurationSet M J :=
      finMapConfiguration_mem M hA
    have hAC : configurationFinMap C = A := by
      dsimp [C]
      exact configurationFinMap_finMapConfiguration A
    have hs := supportOrientation_mem
      (configurationPolynomial weight coeff Cstar)
    have hupper : ℓ z ≤
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      rw [hzPos, ← hAC]
      rw [orientedSatelliteSupport_configuration]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt M.closedUnitBallVolume_pos)
      exact (sign_mul_le_abs hs).trans (hstarMax C hC)
    have heq : ℓ z =
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      apply le_antisymm hupper
      simpa [ℓ, Cstar, orientedSatelliteSupport_self] using hstarLeZ
    have hsupport :
        M.closedUnitBallVolume *
          (1 * (supportOrientation
            (configurationPolynomial weight coeff Cstar) *
              configurationPolynomial weight coeff C)) =
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      calc
        M.closedUnitBallVolume *
            (1 * (supportOrientation
              (configurationPolynomial weight coeff Cstar) *
                configurationPolynomial weight coeff C)) =
            M.closedUnitBallVolume *
              (supportOrientation
                (configurationPolynomial weight coeff Cstar) *
                  configurationPolynomial weight coeff C) := by ring
        _ = ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap C)) :=
          (orientedSatelliteSupport_configuration
            M weight coeff Cstar C).symm
        _ = ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) := by rw [hAC]
        _ = ℓ z := by rw [hzPos]
        _ = M.closedUnitBallVolume *
            |configurationPolynomial weight coeff Cstar| := heq
    have habs : |configurationPolynomial weight coeff C| =
        |configurationPolynomial weight coeff Cstar| :=
      abs_eq_of_oriented_signed_scaled_eq M.closedUnitBallVolume_pos hs (Or.inl rfl)
        hsupport
    refine ⟨A, hA, Or.inl hzPos, hC, ?_⟩
    intro D hD
    exact (hstarMax D hD).trans_eq habs.symm
  · let C : SatelliteConfiguration (m + 1) J := finMapConfiguration A
    have hC : C ∈ satelliteConfigurationSet M J :=
      finMapConfiguration_mem M hA
    have hAC : configurationFinMap C = A := by
      dsimp [C]
      exact configurationFinMap_finMapConfiguration A
    have hs := supportOrientation_mem
      (configurationPolynomial weight coeff Cstar)
    have hminusSign :
        - supportOrientation (configurationPolynomial weight coeff Cstar) = 1 ∨
        - supportOrientation (configurationPolynomial weight coeff Cstar) = -1 := by
      rcases hs with h | h <;> simp [h]
    have hupper : ℓ z ≤
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      calc
        ℓ z = ℓ (- MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) := by rw [hzNeg]
        _ = -ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) := by simp
        _ = -ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap C)) := by rw [hAC]
        _ = -(M.closedUnitBallVolume *
            (supportOrientation
              (configurationPolynomial weight coeff Cstar) *
                configurationPolynomial weight coeff C)) := by
          rw [orientedSatelliteSupport_configuration]
          rfl
        _ = M.closedUnitBallVolume *
            ((-supportOrientation
              (configurationPolynomial weight coeff Cstar)) *
                configurationPolynomial weight coeff C) := by ring
        _ ≤ M.closedUnitBallVolume *
            |configurationPolynomial weight coeff Cstar| := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt M.closedUnitBallVolume_pos)
          exact (sign_mul_le_abs hminusSign).trans (hstarMax C hC)
    have heq : ℓ z =
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      apply le_antisymm hupper
      simpa [ℓ, Cstar, orientedSatelliteSupport_self] using hstarLeZ
    have hsupport :
        M.closedUnitBallVolume *
          ((-1) * (supportOrientation
            (configurationPolynomial weight coeff Cstar) *
              configurationPolynomial weight coeff C)) =
        M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
      calc
        M.closedUnitBallVolume *
            ((-1) * (supportOrientation
              (configurationPolynomial weight coeff Cstar) *
                configurationPolynomial weight coeff C)) =
            -(M.closedUnitBallVolume *
              (supportOrientation
                (configurationPolynomial weight coeff Cstar) *
                  configurationPolynomial weight coeff C)) := by ring
        _ = -ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M (configurationFinMap C)) := by
          rw [orientedSatelliteSupport_configuration]
          rfl
        _ = -ℓ (MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) := by rw [hAC]
        _ = ℓ (- MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A) := by simp
        _ = ℓ z := by rw [hzNeg]
        _ = M.closedUnitBallVolume *
            |configurationPolynomial weight coeff Cstar| := heq
    have habs : |configurationPolynomial weight coeff C| =
        |configurationPolynomial weight coeff Cstar| :=
      abs_eq_of_oriented_signed_scaled_eq M.closedUnitBallVolume_pos hs (Or.inr rfl)
        hsupport
    refine ⟨A, hA, Or.inr hzNeg, hC, ?_⟩
    intro D hD
    exact (hstarMax D hD).trans_eq habs.symm

theorem targetRawSupportMaximizer_good
    {m : ℕ} (M : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue Cnet) < weight * η)
    {z : PluckerCoord (m + 1)
      (positiveSatelliteAmbientDim m Cnet.centers)}
    (hz : z ∈ MathlibAnnex.NonemptyCompacts.maxSlice (rawPluckerCompact
      (N := positiveSatelliteAmbientDim m Cnet.centers) M)
        (orientedSatelliteSupport weight (centerValue Cnet)
          (maxSatelliteConfiguration M Cnet.centers
            weight (centerValue Cnet)))) :
    PluckerGeneratorGood M ε z := by
  classical
  rcases rawOrientedSupportMaximizer_isAbsolutePolynomialMaximizer
      M weight (centerValue Cnet) hz with
    ⟨A, hA, hzA, hC, hmax⟩
  let C : SatelliteConfiguration (m + 1) Cnet.centers :=
    finMapConfiguration A
  have hAC : configurationFinMap C = A := by
    dsimp [C]
    exact configurationFinMap_finMapConfiguration A
  refine ⟨A, hA, ?_, hzA⟩
  intro x hx
  rcases finiteNet_absoluteMaximizer_satellites_one_sub_epsilon
      M hη0 hηD hε H Cnet hweight hgap hC hmax hx with ⟨a, ha⟩
  have hcoord : |C.2 a x| ≤ ‖configurationFinMap C x‖ := by
    have := norm_le_pi_norm (configurationFinMap C x)
      (Fin.natAdd (m + 1) (Fintype.equivFin Cnet.centers a))
    simpa [configurationFinMap_apply_satellite, Real.norm_eq_abs] using this
  rw [hAC] at hcoord
  exact ha.trans_le hcoord

private theorem exists_commonGoodRaw
    {m : ℕ} (MX MY : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax MY) (hε : 0 < ε)
    (H : NearMaxInverseBound MY η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget MY (centerValue Cnet) < weight * η)
    (hHull :
      MathlibAnnex.PluckerBody.body MX (positiveSatelliteAmbientDim m Cnet.centers) =
        MathlibAnnex.PluckerBody.body MY (positiveSatelliteAmbientDim m Cnet.centers)) :
    ∃ z : PluckerCoord (m + 1)
        (positiveSatelliteAmbientDim m Cnet.centers),
      z ∈ MathlibAnnex.PluckerBody.generators MX
        (positiveSatelliteAmbientDim m Cnet.centers) ∧
      z ∈ MathlibAnnex.PluckerBody.generators MY
        (positiveSatelliteAmbientDim m Cnet.centers) ∧
      PluckerGeneratorGood MY ε z := by
  classical
  let RX := rawPluckerCompact
    (N := positiveSatelliteAmbientDim m Cnet.centers) MX
  let RY := rawPluckerCompact
    (N := positiveSatelliteAmbientDim m Cnet.centers) MY
  let Cstar : SatelliteConfiguration (m + 1) Cnet.centers :=
    maxSatelliteConfiguration MY Cnet.centers weight (centerValue Cnet)
  let ℓ := orientedSatelliteSupport weight (centerValue Cnet) Cstar
  have hHull' : convexHull ℝ (RX : Set (PluckerCoord (m + 1) (positiveSatelliteAmbientDim m Cnet.centers))) = convexHull ℝ (RY : Set (PluckerCoord (m + 1) (positiveSatelliteAmbientDim m Cnet.centers))) := by
    simpa [RX, RY, rawPluckerCompact, MathlibAnnex.PluckerBody.body] using hHull
  exact MathlibAnnex.exists_common_pi
    RX RY hHull' ℓ (PluckerGeneratorGood MY ε)
    (fun z hz => targetRawSupportMaximizer_good
      MY hη0 hηD hε H Cnet hweight hgap (by simpa [RY, ℓ, Cstar] using hz))

structure AlmostIsometryMatch {m : ℕ}
    (MX MY : NormModel (m + 1)) (ε : ℝ) where
  N : ℕ
  z : PluckerCoord (m + 1) N
  sourceMap : Coord (m + 1) →L[ℝ] SupCoord N
  targetMap : Coord (m + 1) →L[ℝ] SupCoord N
  sourceContraction : MX.IsContraction sourceMap
  targetContraction : MY.IsContraction targetMap
  targetAlmost : FinMapAlmostIsometric MY ε targetMap
  sourceSigned :
    z = MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MX sourceMap ∨
      z = - MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MX sourceMap
  targetSigned :
    z = MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MY targetMap ∨
      z = - MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MY targetMap

theorem exists_almostIsometryMatch_at_satelliteDimension
    {m : ℕ} (MX MY : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax MY) (hε : 0 < ε)
    (H : NearMaxInverseBound MY η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget MY (centerValue Cnet) < weight * η)
    (hHull :
      MathlibAnnex.PluckerBody.body MX (positiveSatelliteAmbientDim m Cnet.centers) =
        MathlibAnnex.PluckerBody.body MY (positiveSatelliteAmbientDim m Cnet.centers)) :
    Nonempty (AlmostIsometryMatch MX MY ε) := by
  classical
  rcases exists_commonGoodRaw MX MY hη0 hηD hε H Cnet
      hweight hgap hHull with ⟨z, hzX, _hzY, hgood⟩
  rcases hzX with ⟨T, hT, hTsign⟩
  rcases hgood with ⟨A, hA, hAlmost, hAsign⟩
  exact ⟨{
    N := positiveSatelliteAmbientDim m Cnet.centers
    z := z
    sourceMap := T
    targetMap := A
    sourceContraction := hT
    targetContraction := hA
    targetAlmost := hAlmost
    sourceSigned := hTsign
    targetSigned := hAsign
  }⟩

theorem exists_almostIsometryMatch_of_all_body_eq
    {m : ℕ} (MX MY : NormModel (m + 1)) {ε : ℝ} (hε : 0 < ε)
    (hBodies : ∀ N : ℕ, MathlibAnnex.PluckerBody.body MX N = MathlibAnnex.PluckerBody.body MY N) :
    Nonempty (AlmostIsometryMatch MX MY ε) := by
  let η : ℝ := detMax MY / 2
  have hD : 0 < detMax MY := detMax_pos MY
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hηD : η < detMax MY := by
    dsimp [η]
    linarith
  rcases exists_goodSatellitePackage MY hη hηD hε with
    ⟨H, Cnet, weight, hweight, hgap, _hselectedGood⟩
  exact exists_almostIsometryMatch_at_satelliteDimension
    MX MY hη.le hηD hε H Cnet hweight hgap
    (hBodies (positiveSatelliteAmbientDim m Cnet.centers))

end MathlibAnnex.FiniteRecovery
