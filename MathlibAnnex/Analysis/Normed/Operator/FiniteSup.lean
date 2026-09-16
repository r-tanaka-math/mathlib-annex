import MathlibAnnex.Analysis.Normed.Dual.Satellite
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport
import MathlibAnnex.LinearAlgebra.Matrix.VolumeScaledMaximalMinor

noncomputable section
set_option autoImplicit false
open Set Module
open scoped BigOperators NNReal
namespace MathlibAnnex.FiniteSup
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

universe v
namespace Internal
end Internal
namespace Bridge
end Bridge
open Internal Bridge

private noncomputable def finiteRowEquiv (n : ℕ) (J : Type u) [Fintype J] :
    Sum (Fin n) J ≃ Fin (n + Fintype.card J) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Fintype.equivFin J)).trans
    finSumFinEquiv

@[simp] private theorem finiteRowEquiv_inl (n : ℕ) (J : Type u) [Fintype J]
    (i : Fin n) :
    finiteRowEquiv n J (Sum.inl i) = Fin.castAdd (Fintype.card J) i := by
  simp [finiteRowEquiv]

@[simp] private theorem finiteRowEquiv_inr (n : ℕ) (J : Type u) [Fintype J]
    (a : J) :
    finiteRowEquiv n J (Sum.inr a) =
      Fin.natAdd n (Fintype.equivFin J a) := by
  simp [finiteRowEquiv]

@[simp] private theorem finiteRowEquiv_symm_castAdd (n : ℕ) (J : Type u)
    [Fintype J] (i : Fin n) :
    (finiteRowEquiv n J).symm (Fin.castAdd (Fintype.card J) i) =
      Sum.inl i := by
  apply (finiteRowEquiv n J).injective
  simp only [Equiv.apply_symm_apply, finiteRowEquiv_inl]

@[simp] private theorem finiteRowEquiv_symm_natAdd (n : ℕ) (J : Type u)
    [Fintype J] (a : J) :
    (finiteRowEquiv n J).symm
      (Fin.natAdd n (Fintype.equivFin J a)) = Sum.inr a := by
  apply (finiteRowEquiv n J).injective
  simp only [Equiv.apply_symm_apply, finiteRowEquiv_inr]

private noncomputable def reindexPiCLM {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e.symm k)

@[simp] private theorem reindexPiCLM_apply {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : ι → ℝ) (k : κ) :
    reindexPiCLM e x k = x (e.symm k) := rfl

private theorem norm_reindexPiCLM {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : ι → ℝ) :
    ‖reindexPiCLM e x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
    intro k
    simpa only [reindexPiCLM_apply] using
      norm_le_pi_norm x (e.symm k)
  · apply (pi_norm_le_iff_of_nonneg
      (norm_nonneg (reindexPiCLM e x))).2
    intro i
    simpa only [reindexPiCLM_apply, Equiv.symm_apply_apply] using
      norm_le_pi_norm (reindexPiCLM e x) (e i)

private def Internal.configurationRow {n : ℕ} {J : Type u}
    (C : SatelliteConfiguration n J) :
    Sum (Fin n) J → (Coord n →L[ℝ] ℝ)
  | Sum.inl i => C.1 i
  | Sum.inr a => C.2 a

noncomputable def configurationMap {n : ℕ} {J : Type u} [Fintype J]
    (C : SatelliteConfiguration n J) :
    Coord n →L[ℝ] (Sum (Fin n) J → ℝ) :=
  ContinuousLinearMap.pi (configurationRow C)

@[simp] private theorem Internal.configurationMap_apply {n : ℕ} {J : Type u} [Fintype J]
    (C : SatelliteConfiguration n J) (x : Coord n)
    (k : Sum (Fin n) J) :
    configurationMap C x k = configurationRow C k x := rfl

theorem configurationMap_norm_le_model {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J) (x : Coord n) :
    ‖configurationMap C x‖ ≤ M.p x := by
  apply (pi_norm_le_iff_of_nonneg (apply_nonneg M.p x)).2
  intro k
  cases k with
  | inl i =>
      simpa [configurationMap, configurationRow, Real.norm_eq_abs] using hC.1 i x
  | inr a =>
      simpa [configurationMap, configurationRow, Real.norm_eq_abs] using hC.2 a x

theorem configurationMap_norm_gt_of_satellite {n : ℕ} {J : Type u}
    [Fintype J] (C : SatelliteConfiguration n J) (x : Coord n)
    {a : J} {t : ℝ} (ha : t < |C.2 a x|) :
    t < ‖configurationMap C x‖ := by
  have hcoord : |configurationMap C x (Sum.inr a)| ≤
      ‖configurationMap C x‖ := by
    simpa [Real.norm_eq_abs] using
      norm_le_pi_norm (configurationMap C x) (Sum.inr a)
  simpa [configurationMap, configurationRow] using ha.trans_le hcoord

private theorem Internal.maxNetConfigurationMap_unit_lower {n : ℕ}
    (M : NormModel n) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := n) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue Cnet) < weight * η)
    {x : Coord n} (hx : M.p x = 1) :
    1 - ε <
      ‖configurationMap
        (maxSatelliteConfiguration M Cnet.centers weight (centerValue Cnet)) x‖ := by
  rcases maxNetSatelliteConfiguration_satellites_one_sub_epsilon
      M hη0 hηD hε H Cnet hweight hgap hx with ⟨a, ha⟩
  exact configurationMap_norm_gt_of_satellite _ _ ha

theorem maxNetConfigurationMap_lower_of_ne_zero {n : ℕ}
    (M : NormModel n) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := n) H.K
      (satelliteRadiusNNReal ε H.K hε H.K_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue Cnet) < weight * η)
    {x : Coord n} (hx0 : x ≠ 0) :
    (1 - ε) * M.p x <
      ‖configurationMap
        (maxSatelliteConfiguration M Cnet.centers weight (centerValue Cnet)) x‖ := by
  let t : ℝ := M.p x
  have ht : 0 < t := by
    have htnonneg : 0 ≤ t := apply_nonneg M.p x
    have htne : t ≠ 0 := by
      intro hzero
      exact hx0 (M.eq_zero_of_apply_eq_zero (by simpa [t] using hzero))
    exact lt_of_le_of_ne htnonneg (Ne.symm htne)
  let u : Coord n := t⁻¹ • x
  have hu : M.p u = 1 := by
    change M.p (t⁻¹ • x) = 1
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹ * t = 1
    exact inv_mul_cancel₀ ht.ne' 
  have hunit := maxNetConfigurationMap_unit_lower
    M hη0 hηD hε H Cnet hweight hgap hu
  have hmap :
      configurationMap
        (maxSatelliteConfiguration M Cnet.centers weight (centerValue Cnet)) u =
      t⁻¹ • configurationMap
        (maxSatelliteConfiguration M Cnet.centers weight (centerValue Cnet)) x := by
    simp [u]
  rw [hmap, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)] at hunit
  have hunit' :
      1 - ε <
        ‖configurationMap
          (maxSatelliteConfiguration M Cnet.centers weight (centerValue Cnet)) x‖ / t := by
    simpa [div_eq_mul_inv, mul_comm] using hunit
  exact (lt_div_iff₀ ht).mp hunit' 

abbrev Bridge.satelliteAmbientDim (n : ℕ) (J : Type u) [Fintype J] : ℕ :=
  n + Fintype.card J

noncomputable def Bridge.configurationFinMap {n : ℕ} {J : Type u} [Fintype J]
    (C : SatelliteConfiguration n J) :
    Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J) :=
  (reindexPiCLM (finiteRowEquiv n J)).comp (configurationMap C)

@[simp] theorem Bridge.configurationFinMap_apply_base {n : ℕ} {J : Type u}
    [Fintype J] (C : SatelliteConfiguration n J) (x : Coord n) (i : Fin n) :
    configurationFinMap C x (Fin.castAdd (Fintype.card J) i) = C.1 i x := by
  simp [configurationFinMap, configurationMap, configurationRow]

@[simp] theorem Bridge.configurationFinMap_apply_satellite {n : ℕ} {J : Type u}
    [Fintype J] (C : SatelliteConfiguration n J) (x : Coord n) (a : J) :
    configurationFinMap C x (Fin.natAdd n (Fintype.equivFin J a)) = C.2 a x := by
  simp [configurationFinMap, configurationMap, configurationRow]

theorem Bridge.configurationFinMap_norm {n : ℕ} {J : Type u} [Fintype J]
    (C : SatelliteConfiguration n J) (x : Coord n) :
    ‖configurationFinMap C x‖ = ‖configurationMap C x‖ := by
  exact norm_reindexPiCLM (finiteRowEquiv n J) (configurationMap C x)

theorem Bridge.configurationFinMap_norm_le_model {n : ℕ} {J : Type u}
    [Fintype J] (M : NormModel n) {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J) (x : Coord n) :
    ‖configurationFinMap C x‖ ≤ M.p x := by
  rw [configurationFinMap_norm]
  exact configurationMap_norm_le_model M hC x

noncomputable def Bridge.finMapBaseRow {n : ℕ} {J : Type u} [Fintype J]
    (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J)) (i : Fin n) :
    Coord n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (Fin.castAdd (Fintype.card J) i)).comp A

noncomputable def Bridge.finMapSatelliteRow {n : ℕ} {J : Type u} [Fintype J]
    (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J)) (a : J) :
    Coord n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (Fin.natAdd n (Fintype.equivFin J a))).comp A

noncomputable def Bridge.finMapConfiguration {n : ℕ} {J : Type u} [Fintype J]
    (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J)) :
    SatelliteConfiguration n J :=
  (finMapBaseRow A, finMapSatelliteRow A)

@[simp] theorem Bridge.finMapConfiguration_base_apply {n : ℕ} {J : Type u}
    [Fintype J] (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J))
    (i : Fin n) (x : Coord n) :
    (finMapConfiguration A).1 i x =
      A x (Fin.castAdd (Fintype.card J) i) := rfl

@[simp] theorem Bridge.finMapConfiguration_satellite_apply {n : ℕ} {J : Type u}
    [Fintype J] (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J))
    (a : J) (x : Coord n) :
    (finMapConfiguration A).2 a x =
      A x (Fin.natAdd n (Fintype.equivFin J a)) := rfl

@[simp] theorem Bridge.finMapConfiguration_configurationFinMap {n : ℕ} {J : Type u}
    [Fintype J] (C : SatelliteConfiguration n J) :
    finMapConfiguration (configurationFinMap C) = C := by
  apply Prod.ext
  · funext i
    ext x
    simp [finMapConfiguration, finMapBaseRow]
  · funext a
    ext x
    simp [finMapConfiguration, finMapSatelliteRow]

@[simp] theorem Bridge.configurationFinMap_finMapConfiguration {n : ℕ} {J : Type u}
    [Fintype J]
    (A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J)) :
    configurationFinMap (finMapConfiguration A) = A := by
  ext x k
  obtain ⟨i | a, rfl⟩ := (finiteRowEquiv n J).surjective k
  · simp [configurationFinMap, finMapConfiguration, configurationRow]
    change A x (Fin.castAdd (Fintype.card J) i) =
      A x (Fin.castAdd (Fintype.card J) i)
    rfl
  · simp [configurationFinMap, finMapConfiguration, configurationRow]
    change A x (Fin.natAdd n (Fintype.equivFin J a)) =
      A x (Fin.natAdd n (Fintype.equivFin J a))
    rfl

theorem Bridge.finMapConfiguration_mem {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n)
    {A : Coord n →L[ℝ] SupCoord (satelliteAmbientDim n J)}
    (hA : M.IsContraction A) :
    finMapConfiguration A ∈ satelliteConfigurationSet M J := by
  constructor
  · intro i x
    have hcoord : |A x (Fin.castAdd (Fintype.card J) i)| ≤ ‖A x‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (A x) (Fin.castAdd (Fintype.card J) i)
    exact hcoord.trans (hA x)
  · intro a x
    have hcoord : |A x (Fin.natAdd n (Fintype.equivFin J a))| ≤ ‖A x‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (A x) (Fin.natAdd n (Fintype.equivFin J a))
    exact hcoord.trans (hA x)

theorem Bridge.configuration_contraction_iff {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) (C : SatelliteConfiguration n J) :
    M.IsContraction (configurationFinMap C) ↔
      C ∈ satelliteConfigurationSet M J := by
  constructor
  · intro h
    simpa using finMapConfiguration_mem M h
  · intro h
    exact configurationFinMap_norm_le_model M h

def FinMapAlmostIsometric {n N : ℕ} (M : NormModel n) (ε : ℝ)
    (A : Coord n →L[ℝ] SupCoord N) : Prop :=
  ∀ x : Coord n, M.p x = 1 → 1 - ε < ‖A x‖

theorem FinMapAlmostIsometric.lower_of_ne_zero {n N : ℕ} {M : NormModel n} {ε : ℝ}
    {A : Coord n →L[ℝ] SupCoord N}
    (hA : FinMapAlmostIsometric M ε A)
    {x : Coord n} (hx : x ≠ 0) :
    (1 - ε) * M.p x < ‖A x‖ := by
  have hpx_nonneg : 0 ≤ M.p x := apply_nonneg M.p x
  have hpx_ne : M.p x ≠ 0 := by
    intro hzero
    exact hx (M.eq_zero_of_apply_eq_zero hzero)
  have hpx : 0 < M.p x := lt_of_le_of_ne hpx_nonneg (Ne.symm hpx_ne)
  let u : Coord n := (M.p x)⁻¹ • x
  have hu : M.p u = 1 := by
    rw [show u = (M.p x)⁻¹ • x by rfl, map_smul_eq_mul]
    simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpx),
      inv_mul_cancel₀ hpx.ne']
  have hlower := hA u hu
  have hnorm : ‖A u‖ = (M.p x)⁻¹ * ‖A x‖ := by
    simp [u, norm_smul]
  rw [hnorm] at hlower
  calc
    (1 - ε) * M.p x = M.p x * (1 - ε) := mul_comm _ _
    _ < M.p x * ((M.p x)⁻¹ * ‖A x‖) :=
      mul_lt_mul_of_pos_left hlower hpx
    _ = ‖A x‖ := by simp [hpx.ne']

end MathlibAnnex.FiniteSup
