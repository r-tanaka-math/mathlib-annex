import MathlibAnnex.Analysis.Normed.Operator.FiniteRecovery
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport
import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinorFactorization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Linear recovery with the selected leading chart, exact signed volume,
and the source-to-target factorization. Private witnesses stay in this module. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Module
open scoped BigOperators NNReal Matrix
namespace MathlibAnnex.PluckerRecovery
namespace Internal
universe u
open Satellite FiniteSup FiniteSup.Bridge PluckerSupport FiniteRecovery
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

private theorem seminorm_framePreimage_le {n : ℕ} (M : NormModel n) {η : ℝ} (H : NearMaxInverseBound M η) {B : DualFrame n}
    (h : B ∈ nearMaxFrames M η) (c : Coord n) : M.p (framePreimage B c) ≤ H.boundConstant * ‖c‖ := by
  exact H.bound (toModelFrame_near M h) c

private theorem detMax_pos {n : ℕ} (M : NormModel n) : 0 < detMax M :=
  DeterminantFrame.determinantMaximum_pos (modelBasis M)

private theorem nearMaxFrame_det_ne_zero {n : ℕ} (M : NormModel n) {η : ℝ}
    (hη : η < detMax M) {B : DualFrame n} (hB : B ∈ nearMaxFrames M η) : frameDet B ≠ 0 :=
  DeterminantFrame.nearMaxFrame_det_ne_zero (modelBasis M) hη (toModelFrame_near M hB)

private abbrev SupCoord (n : ℕ) := Fin n → ℝ

variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}
private noncomputable instance centerFintype (C : FiniteCoefficientNet (n := n) K ρ) :
    Fintype C.centers :=
  C.finite_centers.fintype



variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}
private def centerValue (C : FiniteCoefficientNet (n := n) K ρ) (c : C.centers) :
    Coord n := c.1

private def satelliteRadius (ε K : ℝ) : ℝ := min ε 1 / (8 * K)

private theorem satelliteRadius_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    0 < satelliteRadius ε K := by
  exact div_pos (lt_min hε zero_lt_one) (mul_pos (by norm_num) hK)

private theorem two_mul_bound_mul_satelliteRadius_lt_half {ε K : ℝ}
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

private abbrev MinorIndex (n N : ℕ) := MathlibAnnex.Matrix.MaximalMinorIndex n (Fin N)
private abbrev PluckerCoord (n N : ℕ) := MinorIndex n N → ℝ
private abbrev clmMatrix {n N : ℕ} (A : Coord n →L[ℝ] SupCoord N) := LinearMap.toMatrix' A.toLinearMap
private abbrev maximalMinor := @MathlibAnnex.Matrix.maximalMinor
private abbrev maximalMinors := @MathlibAnnex.Matrix.maximalMinors
private abbrev selectedSubmatrix := @MathlibAnnex.Matrix.maximalSubmatrix
private abbrev minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding
private abbrev selectedSubmatrix_minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.maximalSubmatrix_ofOrderEmbedding
private abbrev maximalMinor_minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.maximalMinor_ofOrderEmbedding
variable {m : ℕ} {J : Type u} [Fintype J]

private abbrev positiveSatelliteAmbientDim (m : ℕ) (J : Type u) [Fintype J] : ℕ :=
  (m + 1) + Fintype.card J

private def baseRowIndex (J : Type u) [Fintype J] (i : Fin (m + 1)) :
    Fin (positiveSatelliteAmbientDim m J) :=
  Fin.castAdd (Fintype.card J) i

private noncomputable def baseRowOrderEmb (m : ℕ) (J : Type u) [Fintype J] :
    Fin (m + 1) ↪o Fin (positiveSatelliteAmbientDim m J) :=
  Fin.castAddOrderEmb (Fintype.card J)

@[simp] private theorem baseRowOrderEmb_apply (i : Fin (m + 1)) :
    baseRowOrderEmb m J i = baseRowIndex J i := by
  rfl
private noncomputable def baseMinorIndex :
    MinorIndex (m + 1) (positiveSatelliteAmbientDim m J) :=
  minorIndexOfOrderEmbedding (baseRowOrderEmb m J)
private theorem maximalMinor_configurationFinMap_base
    (C : SatelliteConfiguration (m + 1) J) :
    maximalMinor (clmMatrix (configurationFinMap C))
      (baseMinorIndex (m := m) (J := J)) = frameDet C.1 := by
  unfold baseMinorIndex
  unfold maximalMinor minorIndexOfOrderEmbedding
  rw [MathlibAnnex.Matrix.maximalMinor_ofOrderEmbedding]
  congr 1
  ext i j
  simp [baseRowOrderEmb, clmMatrix, DeterminantFrame.frameMatrix, Pi.basisFun_apply]

private noncomputable def rawPluckerCompact {n N : ℕ} (M : NormModel n) :
    TopologicalSpace.NonemptyCompacts (PluckerCoord n N) where
  carrier := MathlibAnnex.PluckerBody.generators M N
  isCompact' := MathlibAnnex.PluckerBody.isCompact_generators M
  nonempty' := MathlibAnnex.PluckerBody.generators_nonempty M

private theorem clm_injective_of_maximalMinor_ne_zero {n N : ℕ}
    (A : Coord n →L[ℝ] SupCoord N) (s : MinorIndex n N)
    (hs : maximalMinor (clmMatrix A) s ≠ 0) : Function.Injective A := by
  have h := MathlibAnnex.Matrix.mulVec_injective_of_maximalMinor_ne_zero (clmMatrix A) s hs
  intro x y hxy
  apply h
  simpa [clmMatrix, LinearMap.toMatrix'_mulVec] using hxy
private noncomputable abbrev leadingMinorIndex (m q : ℕ) :
    MinorIndex (m + 1) ((m + 1) + q) :=
  minorIndexOfOrderEmbedding (Fin.castAddOrderEmb q)

/-- A sign used to record whether a raw point is the positive or negative
normalized Plücker generator. -/
private structure PluckerSign where
  value : ℝ
  value_eq : value = 1 ∨ value = -1

namespace PluckerSign

/-- Positive raw orientation. -/
private def positive : PluckerSign := ⟨1, Or.inl rfl⟩

/-- Negative raw orientation. -/
private def negative : PluckerSign := ⟨-1, Or.inr rfl⟩

@[simp] private theorem positive_value : positive.value = 1 := rfl
@[simp] private theorem negative_value : negative.value = -1 := rfl

private theorem value_ne_zero (s : PluckerSign) : s.value ≠ 0 := by
  rcases s.value_eq with h | h <;> norm_num [h]

private theorem value_sq (s : PluckerSign) : s.value * s.value = 1 := by
  rcases s.value_eq with h | h <;> norm_num [h]

private theorem abs_value (s : PluckerSign) : |s.value| = 1 := by
  rcases s.value_eq with h | h <;> norm_num [h]

end PluckerSign

/-- The target support property strengthened by a nonzero leading Plücker
coordinate. -/
private def AnchoredPluckerGeneratorGood {m q : ℕ}
    (M : NormModel (m + 1)) (ε : ℝ)
    (z : PluckerCoord (m + 1) ((m + 1) + q)) : Prop :=
  PluckerGeneratorGood M ε z ∧ z (leadingMinorIndex m q) ≠ 0

/-- Every oriented satellite-support maximizer has nonzero canonical base
coordinate.  The proof uses the strict determinant gap before any
lexicographic refinement is performed. -/
private theorem targetRawSupportMaximizer_leading_ne_zero
    {m : ℕ} (M : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (_hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant _hε H.boundConstant_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue Cnet) < weight * η)
    {z : PluckerCoord (m + 1)
      (positiveSatelliteAmbientDim m Cnet.centers)}
    (hz : z ∈ MathlibAnnex.NonemptyCompacts.maxSlice (rawPluckerCompact
      (N := positiveSatelliteAmbientDim m Cnet.centers) M)
        (orientedSatelliteSupport weight (centerValue Cnet)
          (maxSatelliteConfiguration M Cnet.centers
            weight (centerValue Cnet)))) :
    z (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0 := by
  -- [R11-API-CHECK:ANC-001]
  classical
  rcases exists_contraction_maximizing_abs_configurationPolynomial_of_mem_maxSlice
      M weight (centerValue Cnet) hz with
    ⟨A, hA, hzA, hC, hmax⟩
  let C : SatelliteConfiguration (m + 1) Cnet.centers :=
    finMapConfiguration A
  have hAC : configurationFinMap C = A := by
    simp [C]
  have hnear : C.1 ∈ nearMaxFrames M η :=
    absoluteMaximizer_base_nearMax M hη0 hweight (centerValue Cnet)
      hgap hC hmax
  have hdet : frameDet C.1 ≠ 0 :=
    nearMaxFrame_det_ne_zero M hηD hnear
  have hminor :
      maximalMinor (clmMatrix A)
        (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0 := by
    rw [← hAC, maximalMinor_configurationFinMap_base]
    exact hdet
  have hnormalized :
      MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors M A
        (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0 := by
    -- `closedUnitBallVolume` and the selected base determinant are both nonzero.
    simp [MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors, MathlibAnnex.Matrix.maximalMinors,
      M.closedUnitBallVolume_pos.ne', hminor]
  rcases hzA with hzA | hzA
  · simpa [hzA] using hnormalized
  · rw [hzA]
    simpa using neg_ne_zero.mpr hnormalized

/-- Every target support maximizer is both almost isometric and anchored at the
canonical leading minor. -/
private theorem targetRawSupportMaximizer_anchoredGood
    {m : ℕ} (M : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (centerValue Cnet) < weight * η)
    {z : PluckerCoord (m + 1)
      (positiveSatelliteAmbientDim m Cnet.centers)}
    (hz : z ∈ MathlibAnnex.NonemptyCompacts.maxSlice (rawPluckerCompact
      (N := positiveSatelliteAmbientDim m Cnet.centers) M)
        (orientedSatelliteSupport weight (centerValue Cnet)
          (maxSatelliteConfiguration M Cnet.centers
            weight (centerValue Cnet)))) :
    PluckerGeneratorGood M ε z ∧
      z (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0 := by
  exact ⟨targetRawSupportMaximizer_good M hη0 hηD hε H Cnet
      hweight hgap hz,
    targetRawSupportMaximizer_leading_ne_zero M hη0 hηD hε H Cnet
      hweight hgap hz⟩

/-- Equality of the source and target Plücker bodies yields a common raw point
which is target-almost-isometric and has a nonzero canonical leading
coordinate. -/
private theorem exists_commonAnchoredRaw
    {m : ℕ} (MX MY : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax MY) (hε : 0 < ε)
    (H : NearMaxInverseBound MY η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos))
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
      PluckerGeneratorGood MY ε z ∧
      z (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0 := by
  -- [R11-API-CHECK:ANC-002]
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
    RX RY hHull' ℓ
    (fun z => PluckerGeneratorGood MY ε z ∧
      z (baseMinorIndex (m := m) (J := Cnet.centers)) ≠ 0)
    (fun z hz => targetRawSupportMaximizer_anchoredGood
      MY hη0 hηD hε H Cnet hweight hgap
      (by simpa [RY, ℓ, Cstar] using hz))

/-- Common source/target maps with a fixed nonzero leading Plücker coordinate.
The ambient dimension is stored as `(m+1)+q`, so all later chart calculations
use the first square block and the final `q` tail rows. -/
private structure AnchoredAlmostIsometryMatch {m : ℕ}
    (MX MY : NormModel (m + 1)) (ε : ℝ) where
  q : ℕ
  z : PluckerCoord (m + 1) ((m + 1) + q)
  sourceMap : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + q)
  targetMap : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + q)
  isContraction_sourceMap : MX.IsContraction sourceMap
  isContraction_targetMap : MY.IsContraction targetMap
  finMapAlmostIsometric_targetMap : FinMapAlmostIsometric MY ε targetMap
  sourceSign : PluckerSign
  targetSign : PluckerSign
  eq_sourceSign_smul_ballVolumeScaledMaximalMinors : z = sourceSign.value • MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MX sourceMap
  eq_targetSign_smul_ballVolumeScaledMaximalMinors : z = targetSign.value • MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors MY targetMap
  apply_leadingMinorIndex_ne_zero : z (leadingMinorIndex m q) ≠ 0

/-- Convert the old `z = v ∨ z = -v` representation into an explicit sign. -/
private theorem exists_sign_representation {ι : Type*} [Fintype ι]
    {z v : ι → ℝ} (h : z = v ∨ z = -v) :
    ∃ s : PluckerSign, z = s.value • v := by
  rcases h with h | h
  · exact ⟨PluckerSign.positive, by simp [h]⟩
  · exact ⟨PluckerSign.negative, by simp [h]⟩

/-- Fixed-satellite-dimension anchored extraction. -/
private theorem nonempty_anchoredAlmostIsometryMatch_at_satelliteDimension
    {m : ℕ} (MX MY : NormModel (m + 1)) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax MY) (hε : 0 < ε)
    (H : NearMaxInverseBound MY η)
    (Cnet : FiniteCoefficientNet (n := m + 1) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget MY (centerValue Cnet) < weight * η)
    (hHull :
      MathlibAnnex.PluckerBody.body MX (positiveSatelliteAmbientDim m Cnet.centers) =
        MathlibAnnex.PluckerBody.body MY (positiveSatelliteAmbientDim m Cnet.centers)) :
    Nonempty (AnchoredAlmostIsometryMatch MX MY ε) := by
  -- [R11-API-CHECK:ANC-003]
  classical
  rcases exists_commonAnchoredRaw MX MY hη0 hηD hε H Cnet
      hweight hgap hHull with ⟨z, hzX, _hzY, hgood, hzLead⟩
  rcases hzX with ⟨T, hT, hTsign⟩
  rcases hgood with ⟨A, hA, hAlmost, hAsign⟩
  rcases exists_sign_representation hTsign with ⟨sT, hsT⟩
  rcases exists_sign_representation hAsign with ⟨sA, hsA⟩
  let q := Fintype.card Cnet.centers
  refine ⟨{
    q := q
    z := z
    sourceMap := T
    targetMap := A
    isContraction_sourceMap := hT
    isContraction_targetMap := hA
    finMapAlmostIsometric_targetMap := hAlmost
    sourceSign := sT
    targetSign := sA
    eq_sourceSign_smul_ballVolumeScaledMaximalMinors := hsT
    eq_targetSign_smul_ballVolumeScaledMaximalMinors := hsA
    apply_leadingMinorIndex_ne_zero := ?_
  }⟩
  simpa [q, leadingMinorIndex, positiveSatelliteAmbientDim,
    baseMinorIndex, baseRowOrderEmb] using hzLead

/-- Equality of all finite Plücker bodies produces an anchored match for every
positive distortion parameter. -/
private theorem nonempty_anchoredAlmostIsometryMatch_of_all_body_eq
    {m : ℕ} (MX MY : NormModel (m + 1)) {ε : ℝ} (hε : 0 < ε)
    (hBodies : ∀ N : ℕ, MathlibAnnex.PluckerBody.body MX N = MathlibAnnex.PluckerBody.body MY N) :
    Nonempty (AnchoredAlmostIsometryMatch MX MY ε) := by
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
  exact nonempty_anchoredAlmostIsometryMatch_at_satelliteDimension
    MX MY hη.le hηD hε H Cnet hweight hgap
    (hBodies (positiveSatelliteAmbientDim m Cnet.centers))
private def AnchoredAlmostIsometryMatch.orientationProduct
    {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε) : ℝ :=
  P.sourceSign.value * P.targetSign.value

namespace AnchoredAlmostIsometryMatch

variable {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε)

/-- The orientation product is again a sign. -/
private theorem orientationProduct_eq :
    P.orientationProduct = 1 ∨ P.orientationProduct = -1 := by
  rcases P.sourceSign.value_eq with hs | hs <;>
    rcases P.targetSign.value_eq with ht | ht <;>
      simp [orientationProduct, hs, ht]

/-- The orientation product is nonzero. -/
private theorem orientationProduct_ne_zero : P.orientationProduct ≠ 0 := by
  rcases P.orientationProduct_eq with h | h <;> simp [h]


/-- The orientation product has absolute value one. -/
private theorem orientationProduct_abs : |P.orientationProduct| = 1 := by
  rcases P.orientationProduct_eq with h | h <;> simp [h]

/-- Equality of the common raw point gives the weighted maximal-minor relation
coordinate by coordinate. -/
private theorem volume_mul_maximalMinor_sourceMap_eq
    (s : MinorIndex (m + 1) ((m + 1) + P.q)) :
    MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) s =
      P.orientationProduct * MY.closedUnitBallVolume *
        maximalMinor (clmMatrix P.targetMap) s := by
  -- [R11-API-CHECK:WMI-001]
  have hs := congrFun P.eq_sourceSign_smul_ballVolumeScaledMaximalMinors s
  have ht := congrFun P.eq_targetSign_smul_ballVolumeScaledMaximalMinors s
  have hcommon :
      P.sourceSign.value *
          (MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) s) =
        P.targetSign.value *
          (MY.closedUnitBallVolume * maximalMinor (clmMatrix P.targetMap) s) := by
    calc
      P.sourceSign.value *
          (MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) s) = P.z s := by
        simpa [MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors, MathlibAnnex.Matrix.maximalMinors, smul_eq_mul,
          mul_assoc, mul_left_comm, mul_comm] using hs.symm
      _ = P.targetSign.value *
          (MY.closedUnitBallVolume * maximalMinor (clmMatrix P.targetMap) s) := by
        simpa [MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors, MathlibAnnex.Matrix.maximalMinors, smul_eq_mul,
          mul_assoc, mul_left_comm, mul_comm] using ht
  calc
    MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) s =
        (P.sourceSign.value * P.sourceSign.value) *
          (MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) s) := by
      rw [P.sourceSign.value_sq]
      ring
    _ = P.sourceSign.value *
          (P.targetSign.value *
            (MY.closedUnitBallVolume * maximalMinor (clmMatrix P.targetMap) s)) := by
      rw [mul_assoc, hcommon]
    _ = P.orientationProduct * MY.closedUnitBallVolume *
          maximalMinor (clmMatrix P.targetMap) s := by
      simp [orientationProduct, mul_assoc]

/-- The leading source minor is nonzero. -/
private theorem sourceLeadingMinor_ne_zero :
    maximalMinor (clmMatrix P.sourceMap) (leadingMinorIndex m P.q) ≠ 0 := by
  -- [R11-API-CHECK:WMI-002]
  intro hzero
  have hs := congrFun P.eq_sourceSign_smul_ballVolumeScaledMaximalMinors (leadingMinorIndex m P.q)
  apply P.apply_leadingMinorIndex_ne_zero
  rw [hs]
  simp [MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors, MathlibAnnex.Matrix.maximalMinors, hzero]

/-- The leading target minor is nonzero. -/
private theorem targetLeadingMinor_ne_zero :
    maximalMinor (clmMatrix P.targetMap) (leadingMinorIndex m P.q) ≠ 0 := by
  -- [R11-API-CHECK:WMI-003]
  intro hzero
  have ht := congrFun P.eq_targetSign_smul_ballVolumeScaledMaximalMinors (leadingMinorIndex m P.q)
  apply P.apply_leadingMinorIndex_ne_zero
  rw [ht]
  simp [MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors, MathlibAnnex.Matrix.maximalMinors, hzero]

/-- Both ambient maps are injective, using the fixed leading minor rather than
an existential rank criterion. -/
private theorem sourceMap_injective : Function.Injective P.sourceMap :=
  clm_injective_of_maximalMinor_ne_zero P.sourceMap
    (leadingMinorIndex m P.q) P.sourceLeadingMinor_ne_zero

private theorem targetMap_injective : Function.Injective P.targetMap :=
  clm_injective_of_maximalMinor_ne_zero P.targetMap
    (leadingMinorIndex m P.q) P.targetLeadingMinor_ne_zero

end AnchoredAlmostIsometryMatch

private abbrev matrixCLM {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) :
    Coord n →L[ℝ] SupCoord N := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
@[simp] private theorem matrixCLM_apply {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (x : Coord n) :
    matrixCLM A x = A.mulVec x := rfl
@[simp] private theorem clmMatrix_matrixCLM {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) :
    clmMatrix (matrixCLM A) = A := LinearMap.toMatrix'_toLin' A
private theorem clmMatrix_comp {n k N : ℕ} (A : Coord n →L[ℝ] SupCoord N) (B : Coord k →L[ℝ] Coord n) :
    clmMatrix (A.comp B) = clmMatrix A * clmMatrix B := LinearMap.toMatrix'_comp A.toLinearMap B.toLinearMap
private theorem frameCoordinates_eq_mulVec {n : ℕ} (B : DualFrame n) (x : Coord n) :
    frameCoordinates B x = (dualFrameMatrix B).mulVec x := by
  simpa [frameCoordinates, dualFrameMatrix, DeterminantFrame.coordinateEquiv] using
    DeterminantFrame.frameCoordinates_eq_mulVec (Pi.basisFun ℝ (Fin n)) B x
private theorem positiveSatelliteAmbientDim_fin (m q : ℕ) :
    positiveSatelliteAmbientDim m (Fin q) = (m + 1) + q := by
  simp [positiveSatelliteAmbientDim]

private noncomputable def castFinCLM {n N N' : ℕ} (h : N' = N)
    (A : Coord n →L[ℝ] SupCoord N) : Coord n →L[ℝ] SupCoord N' := by
  subst N'
  exact A

private noncomputable def castMinorIndex {n N N' : ℕ} (h : N' = N)
    (s : MinorIndex n N) : MinorIndex n N' := by
  subst N'
  exact s

private theorem castMinorIndex_symm {n N N' : ℕ} (h : N' = N)
    (s : MinorIndex n N') :
    castMinorIndex h (castMinorIndex h.symm s) = s := by
  subst N'
  rfl

private theorem maximalMinor_castFinCLM {n N N' : ℕ} (h : N' = N)
    (A : Coord n →L[ℝ] SupCoord N) (s : MinorIndex n N) :
    maximalMinor (clmMatrix (castFinCLM h A)) (castMinorIndex h s) =
      maximalMinor (clmMatrix A) s := by
  subst N'
  rfl

@[simp] private theorem castFinCLM_apply {n N N' : ℕ} (h : N' = N)
    (A : Coord n →L[ℝ] SupCoord N) (x : Coord n) (i : Fin N') :
    castFinCLM h A x i = A x (Fin.cast h i) := by
  subst N'
  rfl

private theorem castFinCLM_injective {n N N' : ℕ} (h : N' = N) :
    Function.Injective (castFinCLM h :
      (Coord n →L[ℝ] SupCoord N) → (Coord n →L[ℝ] SupCoord N')) := by
  subst N'
  intro A B hAB
  exact hAB

private theorem castFinCLM_comp {n k N N' : ℕ} (h : N' = N)
    (A : Coord n →L[ℝ] SupCoord N) (B : Coord k →L[ℝ] Coord n) :
    castFinCLM h (A.comp B) = (castFinCLM h A).comp B := by
  subst N'
  rfl

private theorem castBaseMinorIndex_eq_leading (m q : ℕ) :
    castMinorIndex (positiveSatelliteAmbientDim_fin m q).symm
        (baseMinorIndex (m := m) (J := Fin q)) =
      leadingMinorIndex m q := by
  have aux (a b : ℕ) (h : a = b) :
      castMinorIndex (congrArg (fun k => (m + 1) + k) h).symm
        (MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding
          (Fin.castAddOrderEmb (n := m + 1) a)) =
      MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding
        (Fin.castAddOrderEmb (n := m + 1) b) := by
    subst b
    rfl
  exact aux (Fintype.card (Fin q)) q (Fintype.card_fin q)

namespace AnchoredAlmostIsometryMatch

variable {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε)

private noncomputable def sourceMapForConfiguration :
    Coord (m + 1) →L[ℝ]
      SupCoord (positiveSatelliteAmbientDim m (Fin P.q)) :=
  castFinCLM (positiveSatelliteAmbientDim_fin m P.q) P.sourceMap

private noncomputable def targetMapForConfiguration :
    Coord (m + 1) →L[ℝ]
      SupCoord (positiveSatelliteAmbientDim m (Fin P.q)) :=
  castFinCLM (positiveSatelliteAmbientDim_fin m P.q) P.targetMap

/-- Source map read as a base-first satellite configuration. -/
private noncomputable def sourceConfiguration :
    SatelliteConfiguration (m + 1) (Fin P.q) :=
  finMapConfiguration P.sourceMapForConfiguration

/-- Target map read as a base-first satellite configuration. -/
private noncomputable def targetConfiguration :
    SatelliteConfiguration (m + 1) (Fin P.q) :=
  finMapConfiguration P.targetMapForConfiguration

@[simp] private theorem sourceConfiguration_finMap :
    configurationFinMap P.sourceConfiguration =
      P.sourceMapForConfiguration := by
  simp [sourceConfiguration]

@[simp] private theorem targetConfiguration_finMap :
    configurationFinMap P.targetConfiguration =
      P.targetMapForConfiguration := by
  simp [targetConfiguration]

/-- The leading raw source minor is the determinant of the recovered base
configuration. -/
private theorem sourceLeadingMinor_eq_baseDet :
    maximalMinor (clmMatrix P.sourceMap) (leadingMinorIndex m P.q) =
      frameDet P.sourceConfiguration.1 := by
  let hdim := positiveSatelliteAmbientDim_fin m P.q
  let sCard := baseMinorIndex (m := m) (J := Fin P.q)
  let sRaw : MinorIndex (m + 1) ((m + 1) + P.q) :=
    castMinorIndex hdim.symm sCard
  have hsRaw : sRaw = leadingMinorIndex m P.q := by
    exact castBaseMinorIndex_eq_leading m P.q
  have hcast :
      maximalMinor (clmMatrix P.sourceMapForConfiguration) sCard =
        maximalMinor (clmMatrix P.sourceMap) sRaw := by
    have h := maximalMinor_castFinCLM hdim P.sourceMap sRaw
    change maximalMinor (clmMatrix P.sourceMapForConfiguration)
        (castMinorIndex hdim sRaw) =
      maximalMinor (clmMatrix P.sourceMap) sRaw at h
    rw [show castMinorIndex hdim sRaw = sCard by
      exact castMinorIndex_symm hdim sCard] at h
    exact h
  calc
    maximalMinor (clmMatrix P.sourceMap) (leadingMinorIndex m P.q) =
        maximalMinor (clmMatrix P.sourceMap) sRaw := by rw [hsRaw]
    _ = maximalMinor (clmMatrix P.sourceMapForConfiguration) sCard := hcast.symm
    _ = maximalMinor (clmMatrix (configurationFinMap P.sourceConfiguration))
        sCard := by rw [P.sourceConfiguration_finMap]
    _ = frameDet P.sourceConfiguration.1 := by
      simpa [sCard] using
        (maximalMinor_configurationFinMap_base P.sourceConfiguration)

/-- The leading raw target minor is the determinant of the recovered base
configuration. -/
private theorem targetLeadingMinor_eq_baseDet :
    maximalMinor (clmMatrix P.targetMap) (leadingMinorIndex m P.q) =
      frameDet P.targetConfiguration.1 := by
  let hdim := positiveSatelliteAmbientDim_fin m P.q
  let sCard := baseMinorIndex (m := m) (J := Fin P.q)
  let sRaw : MinorIndex (m + 1) ((m + 1) + P.q) :=
    castMinorIndex hdim.symm sCard
  have hsRaw : sRaw = leadingMinorIndex m P.q := by
    exact castBaseMinorIndex_eq_leading m P.q
  have hcast :
      maximalMinor (clmMatrix P.targetMapForConfiguration) sCard =
        maximalMinor (clmMatrix P.targetMap) sRaw := by
    have h := maximalMinor_castFinCLM hdim P.targetMap sRaw
    change maximalMinor (clmMatrix P.targetMapForConfiguration)
        (castMinorIndex hdim sRaw) =
      maximalMinor (clmMatrix P.targetMap) sRaw at h
    rw [show castMinorIndex hdim sRaw = sCard by
      exact castMinorIndex_symm hdim sCard] at h
    exact h
  calc
    maximalMinor (clmMatrix P.targetMap) (leadingMinorIndex m P.q) =
        maximalMinor (clmMatrix P.targetMap) sRaw := by rw [hsRaw]
    _ = maximalMinor (clmMatrix P.targetMapForConfiguration) sCard := hcast.symm
    _ = maximalMinor (clmMatrix (configurationFinMap P.targetConfiguration))
        sCard := by rw [P.targetConfiguration_finMap]
    _ = frameDet P.targetConfiguration.1 := by
      simpa [sCard] using
        (maximalMinor_configurationFinMap_base P.targetConfiguration)

/-- The fixed leading source determinant. -/
private theorem sourceBase_det_ne_zero :
    frameDet P.sourceConfiguration.1 ≠ 0 := by
  -- [R11-API-CHECK:CHT-001]
  rw [← P.sourceLeadingMinor_eq_baseDet]
  exact P.sourceLeadingMinor_ne_zero

/-- The fixed leading target determinant. -/
private theorem targetBase_det_ne_zero :
    frameDet P.targetConfiguration.1 ≠ 0 := by
  -- [R11-API-CHECK:CHT-002]
  rw [← P.targetLeadingMinor_eq_baseDet]
  exact P.targetLeadingMinor_ne_zero

/-- Inverse reconstruction for an arbitrary nondegenerate dual frame. -/
private theorem inverse_mulVec_frameCoordinates_of_det_ne_zero
    {n : ℕ} (B : DualFrame n) (hB : frameDet B ≠ 0)
    (x : Coord n) :
    (dualFrameMatrix B)⁻¹.mulVec (frameCoordinates B x) = x := by
  -- [R11-API-CHECK:CHT-003]
  have hunit : IsUnit (dualFrameMatrix B).det :=
    isUnit_iff_ne_zero.mpr (by simpa [frameDet, dualFrameMatrix, DeterminantFrame.frameDeterminant] using hB)
  rw [frameCoordinates_eq_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.nonsing_inv_mul _ hunit]
  exact Matrix.one_mulVec x

/-- Matrix of the recovered source-to-target map. -/
private noncomputable def inducedMatrix : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (dualFrameMatrix P.targetConfiguration.1)⁻¹ *
    dualFrameMatrix P.sourceConfiguration.1

/-- Recovered coordinate linear map. -/
private noncomputable def inducedLinearMap : Coord (m + 1) →L[ℝ] Coord (m + 1) :=
  matrixCLM P.inducedMatrix

@[simp] private theorem inducedLinearMap_apply (x : Coord (m + 1)) :
    P.inducedLinearMap x =
      (dualFrameMatrix P.targetConfiguration.1)⁻¹.mulVec
        (frameCoordinates P.sourceConfiguration.1 x) := by
  -- [R11-API-CHECK:CHT-004]
  simp [inducedLinearMap, inducedMatrix, matrixCLM_apply,
    Matrix.mulVec_mulVec, frameCoordinates_eq_mulVec]
private theorem volume_mul_frameDet_sourceConfiguration_eq :
    MX.closedUnitBallVolume * frameDet P.sourceConfiguration.1 =
      P.orientationProduct * MY.closedUnitBallVolume *
        frameDet P.targetConfiguration.1 := by
  -- [R11-API-CHECK:CHT-006]
  rw [← P.sourceLeadingMinor_eq_baseDet, ← P.targetLeadingMinor_eq_baseDet]
  exact P.volume_mul_maximalMinor_sourceMap_eq (leadingMinorIndex m P.q)

/-- The generic R09 factorization is applied in the same fixed leading chart. -/
private theorem factorization : P.targetMap.comp P.inducedLinearMap = P.sourceMap := by
  let c : ℝ := P.orientationProduct * MY.closedUnitBallVolume / MX.closedUnitBallVolume
  have hc : c ≠ 0 := div_ne_zero
    (mul_ne_zero P.orientationProduct_ne_zero MY.closedUnitBallVolume_pos.ne') MX.closedUnitBallVolume_pos.ne'
  have hprop : MathlibAnnex.Matrix.MaximalMinorsProportional
      (clmMatrix P.sourceMap) (clmMatrix P.targetMap) c := by
    intro t
    apply mul_left_cancel₀ MX.closedUnitBallVolume_pos.ne'
    calc
      MX.closedUnitBallVolume * maximalMinor (clmMatrix P.sourceMap) t =
          P.orientationProduct * MY.closedUnitBallVolume * maximalMinor (clmMatrix P.targetMap) t :=
        P.volume_mul_maximalMinor_sourceMap_eq t
      _ = MX.closedUnitBallVolume * (c * maximalMinor (clmMatrix P.targetMap) t) := by
        dsimp [c]
        field_simp [MX.closedUnitBallVolume_pos.ne']
  have ht : MathlibAnnex.Matrix.orientedMaximalMinor (clmMatrix P.targetMap) (Fin.castAdd P.q) ≠ 0 := by
    have hn := P.targetLeadingMinor_ne_zero
    change MathlibAnnex.Matrix.maximalMinor (clmMatrix P.targetMap)
      (MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding (Fin.castAddOrderEmb P.q)) ≠ 0 at hn
    rw [MathlibAnnex.Matrix.maximalMinor_ofOrderEmbedding] at hn
    exact hn
  have hf := MathlibAnnex.Matrix.mul_chartFactor_eq_of_maximalMinorsProportional
    (clmMatrix P.sourceMap) (clmMatrix P.targetMap) c hc hprop (Fin.castAdd P.q) ht
  have hsbase : (clmMatrix P.sourceMap).submatrix (Fin.castAdd P.q) id =
      dualFrameMatrix P.sourceConfiguration.1 := by
    ext i j
    simp [sourceConfiguration, sourceMapForConfiguration, clmMatrix, dualFrameMatrix,
      DeterminantFrame.frameMatrix, Pi.basisFun_apply, finMapConfiguration_base_apply,
      castFinCLM_apply, positiveSatelliteAmbientDim]
  have htbase : (clmMatrix P.targetMap).submatrix (Fin.castAdd P.q) id =
      dualFrameMatrix P.targetConfiguration.1 := by
    ext i j
    simp [targetConfiguration, targetMapForConfiguration, clmMatrix, dualFrameMatrix,
      DeterminantFrame.frameMatrix, Pi.basisFun_apply, finMapConfiguration_base_apply,
      castFinCLM_apply, positiveSatelliteAmbientDim]
  have hmat : clmMatrix (P.targetMap.comp P.inducedLinearMap) = clmMatrix P.sourceMap := by
    rw [clmMatrix_comp]
    simpa [inducedLinearMap, inducedMatrix, MathlibAnnex.Matrix.chartFactor, hsbase, htbase] using hf
  apply ContinuousLinearMap.ext
  intro x
  simpa [clmMatrix] using congrArg (fun Q : Matrix (Fin ((m + 1) + P.q)) (Fin (m + 1)) ℝ => Q.mulVec x) hmat
private theorem inducedLinearMap_injective : Function.Injective P.inducedLinearMap := by
  -- [R11-API-CHECK:CHT-011]
  intro x y hxy
  apply P.sourceMap_injective
  have hx := congrArg
    (fun F : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + P.q) => F x)
    P.factorization
  have hy := congrArg
    (fun F : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + P.q) => F y)
    P.factorization
  calc
    P.sourceMap x = P.targetMap (P.inducedLinearMap x) := hx.symm
    _ = P.targetMap (P.inducedLinearMap y) := congrArg P.targetMap hxy
    _ = P.sourceMap y := hy

end AnchoredAlmostIsometryMatch
namespace AnchoredAlmostIsometryMatch

variable {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε)

/-- Strict recovered-map estimate away from the origin. -/
private theorem inducedLinearMap_strict_model_bound
    {x : Coord (m + 1)} (hx : x ≠ 0) :
    (1 - ε) * MY.p (P.inducedLinearMap x) < MX.p x := by
  have hLx : P.inducedLinearMap x ≠ 0 := by
    intro hzero
    exact hx (P.inducedLinearMap_injective (by rw [map_zero]; exact hzero))
  have hlower := P.finMapAlmostIsometric_targetMap.lower_of_ne_zero hLx
  have hfactor : P.targetMap (P.inducedLinearMap x) = P.sourceMap x := by
    simpa using congrArg (fun F : Coord (m + 1) →L[ℝ]
      SupCoord ((m + 1) + P.q) => F x) P.factorization
  rw [hfactor] at hlower
  exact hlower.trans_le (P.isContraction_sourceMap x)

/-- Non-strict recovered-map estimate valid at every vector. -/
private theorem inducedLinearMap_model_bound (x : Coord (m + 1)) :
    (1 - ε) * MY.p (P.inducedLinearMap x) ≤ MX.p x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, mul_zero, le_refl]
  · exact (P.inducedLinearMap_strict_model_bound hx).le

/-- When `ε < 1`, the recovered map is quantitatively bounded from the source
model norm to the target model norm. -/
private theorem inducedLinearMap_model_norm_le
    (hε1 : ε < 1) (x : Coord (m + 1)) :
    MY.p (P.inducedLinearMap x) ≤ (1 - ε)⁻¹ * MX.p x := by
  -- [R11-API-CHECK:LIN-002]
  have hpos : 0 < 1 - ε := sub_pos.mpr hε1
  have h := P.inducedLinearMap_model_bound x
  apply (le_inv_mul_iff₀ hpos).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- The recovered map is algebraically bijective in equal finite dimension. -/
private theorem inducedLinearMap_surjective : Function.Surjective P.inducedLinearMap := by
  -- [R11-API-CHECK:LIN-003]
  exact LinearMap.surjective_of_injective P.inducedLinearMap_injective


/-- The ambient ranges of the common representatives agree.  The forward
inclusion is the factorization `T = A ∘ L`; the reverse inclusion uses
surjectivity of the recovered square map. -/
private theorem ambientRange_eq :
    Set.range P.sourceMap = Set.range P.targetMap := by
  -- [R11-API-CHECK:LIN-004]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨P.inducedLinearMap x, ?_⟩
    simpa using congrArg
      (fun F : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + P.q) => F x)
      P.factorization
  · rintro ⟨x, rfl⟩
    rcases P.inducedLinearMap_surjective x with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hfactor := congrArg
      (fun F : Coord (m + 1) →L[ℝ] SupCoord ((m + 1) + P.q) => F u)
      P.factorization
    simpa [hu] using hfactor.symm

/-- For `ε ≤ 1/2`, the target model norm of the recovered map is bounded by
twice the source model norm. -/
private theorem inducedLinearMap_model_norm_le_two
    (hεhalf : ε ≤ (1 / 2 : ℝ)) (x : Coord (m + 1)) :
    MY.p (P.inducedLinearMap x) ≤ 2 * MX.p x := by
  -- [R11-API-CHECK:LIN-005]
  have hcoeff : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
  have hnonneg : 0 ≤ MY.p (P.inducedLinearMap x) := apply_nonneg MY.p _
  have h := P.inducedLinearMap_model_bound x
  nlinarith

/-- Uniform reference-sup-norm bound used by the compact-limit stage. -/
private theorem inducedLinearMap_reference_norm_le
    (hεhalf : ε ≤ (1 / 2 : ℝ)) (x : Coord (m + 1)) :
    ‖P.inducedLinearMap x‖ ≤
      (2 * MX.upper / MY.lower) * ‖x‖ := by
  -- [R11-API-CHECK:LIN-006]
  have hlow := MY.lower_le (P.inducedLinearMap x)
  have hmid := P.inducedLinearMap_model_norm_le_two hεhalf x
  have hupp := MX.le_upper x
  have hpos : 0 < MY.lower := MY.lower_pos
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).2
  nlinarith

end AnchoredAlmostIsometryMatch
namespace AnchoredAlmostIsometryMatch

variable {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε)

/-- Determinant of the recovered square coordinate map. -/
private noncomputable def inducedDet : ℝ := P.inducedMatrix.det

/-- Matrix form of the ambient factorization. -/
private theorem matrix_factorization :
    clmMatrix P.sourceMap =
      clmMatrix P.targetMap * clmMatrix P.inducedLinearMap := by
  -- [R11-API-CHECK:VOL-004]
  rw [← clmMatrix_comp, P.factorization]

/-- Every source maximal minor is the corresponding target maximal minor times
`det L`. -/
private theorem sourceMinor_eq_targetMinor_mul_inducedDet
    (s : MinorIndex (m + 1) ((m + 1) + P.q)) :
    maximalMinor (clmMatrix P.sourceMap) s =
      maximalMinor (clmMatrix P.targetMap) s * P.inducedDet := by
  -- [R11-API-CHECK:VOL-005]
  rw [P.matrix_factorization]
  simpa only [maximalMinor, inducedDet, inducedLinearMap, clmMatrix_matrixCLM] using
    MathlibAnnex.Matrix.maximalMinor_mul (clmMatrix P.targetMap) (clmMatrix P.inducedLinearMap) s

/-- Signed determinant-volume normalization. -/
private theorem inducedDet_signed_volume :
    MX.closedUnitBallVolume * P.inducedDet =
      P.orientationProduct * MY.closedUnitBallVolume := by
  -- [R11-API-CHECK:VOL-006]
  have hweighted := P.volume_mul_maximalMinor_sourceMap_eq
    (leadingMinorIndex m P.q)
  rw [P.sourceMinor_eq_targetMinor_mul_inducedDet] at hweighted
  have hA := P.targetLeadingMinor_ne_zero
  have hcancel :
      (MX.closedUnitBallVolume * P.inducedDet) *
          maximalMinor (clmMatrix P.targetMap)
            (leadingMinorIndex m P.q) =
        (P.orientationProduct * MY.closedUnitBallVolume) *
          maximalMinor (clmMatrix P.targetMap)
            (leadingMinorIndex m P.q) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hweighted
  exact mul_right_cancel₀ hA hcancel

/-- Exact absolute determinant normalization. -/
private theorem inducedDet_abs_volume :
    MX.closedUnitBallVolume * |P.inducedDet| = MY.closedUnitBallVolume := by
  -- [R11-API-CHECK:VOL-007]
  have h := congrArg abs P.inducedDet_signed_volume
  rw [abs_mul, abs_of_pos MX.closedUnitBallVolume_pos,
    abs_mul, P.orientationProduct_abs, one_mul,
    abs_of_pos MY.closedUnitBallVolume_pos] at h
  exact h

/-- In particular the recovered square map is nonsingular. -/
private theorem inducedDet_ne_zero : P.inducedDet ≠ 0 := by
  intro hzero
  have h := P.inducedDet_abs_volume
  rw [hzero, abs_zero, mul_zero] at h
  exact MY.closedUnitBallVolume_pos.ne' h.symm

end AnchoredAlmostIsometryMatch

end Internal
open Internal
structure LinearCertificate {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) (ε : ℝ) where
  q : ℕ
  sourceMap : (Fin (m + 1) → ℝ) →L[ℝ] (Fin ((m + 1) + q) → ℝ)
  targetMap : (Fin (m + 1) → ℝ) →L[ℝ] (Fin ((m + 1) + q) → ℝ)
  linearMap : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)
  factor : targetMap.comp linearMap = sourceMap
  range_sourceMap_eq_range_targetMap : Set.range sourceMap = Set.range targetMap
  injective : Function.Injective linearMap
  surjective : Function.Surjective linearMap
  one_sub_mul_seminorm_linearMap_le : ∀ x, (1 - ε) * MY.p (linearMap x) ≤ MX.p x
  det : ℝ
  det_eq : det = ContinuousLinearMap.det linearMap
  closedUnitBallVolume_mul_abs_det : MX.closedUnitBallVolume * |det| = MY.closedUnitBallVolume

namespace Internal
private noncomputable def AnchoredAlmostIsometryMatch.toRecoveryCertificate
    {m : ℕ} {MX MY : NormModel (m + 1)} {ε : ℝ}
    (P : AnchoredAlmostIsometryMatch MX MY ε) :
    LinearCertificate MX MY ε where
  q := P.q
  sourceMap := P.sourceMap
  targetMap := P.targetMap
  linearMap := P.inducedLinearMap
  factor := P.factorization
  range_sourceMap_eq_range_targetMap := P.ambientRange_eq
  injective := P.inducedLinearMap_injective
  surjective := P.inducedLinearMap_surjective
  one_sub_mul_seminorm_linearMap_le := P.inducedLinearMap_model_bound
  det := P.inducedDet
  det_eq := by
    simp [AnchoredAlmostIsometryMatch.inducedDet,
      AnchoredAlmostIsometryMatch.inducedLinearMap,
      clmMatrix_matrixCLM, ← LinearMap.det_toMatrix', clmMatrix]
  closedUnitBallVolume_mul_abs_det := P.inducedDet_abs_volume

end Internal
theorem nonempty_linearCertificate_of_pluckerBodies_eq
    {m : ℕ} (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hBodies : ∀ N : ℕ, MathlibAnnex.PluckerBody.body MX N = MathlibAnnex.PluckerBody.body MY N) :
    Nonempty (LinearCertificate MX MY ε) := by
  rcases nonempty_anchoredAlmostIsometryMatch_of_all_body_eq MX MY hε hBodies
    with ⟨P⟩
  exact ⟨P.toRecoveryCertificate⟩


namespace LinearCertificate

variable {m : ℕ} {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)} {ε : ℝ}
    (C : LinearCertificate MX MY ε)

/-- Model-norm uniformity at distortions at most one half. -/
theorem seminorm_linearMap_le_two_mul (hεhalf : ε ≤ (1 / 2 : ℝ))
    (x : (Fin (m + 1) → ℝ)) :
    MY.p (C.linearMap x) ≤ 2 * MX.p x := by
  -- [R11-API-CHECK:REC-001]
  have hcoeff : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
  have hnonneg : 0 ≤ MY.p (C.linearMap x) := apply_nonneg MY.p _
  have h := C.one_sub_mul_seminorm_linearMap_le x
  nlinarith

/-- A distortion-independent reference-norm bound for the future sequence. -/
theorem referenceNorm_le (hεhalf : ε ≤ (1 / 2 : ℝ))
    (x : (Fin (m + 1) → ℝ)) :
    ‖C.linearMap x‖ ≤ (2 * MX.upper / MY.lower) * ‖x‖ := by
  -- [R11-API-CHECK:REC-002]
  have hlow := MY.lower_le (C.linearMap x)
  have hmid := C.seminorm_linearMap_le_two_mul hεhalf x
  have hupp := MX.le_upper x
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ MY.lower_pos).2
  nlinarith

end LinearCertificate

end MathlibAnnex.PluckerRecovery
